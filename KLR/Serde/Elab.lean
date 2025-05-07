/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Serde.Attr
import KLR.Serde.Basic
import Lean

/-
# ToCBOR and FromCBOR deriving
-/

namespace KLR.Serde.Elab
open Lean Parser.Term Meta Elab Command Deriving

-- Generate a absolute path for a name
def rootName : Name -> Name
  | .anonymous => .str .anonymous "_root_"
  | .str n s => .str (rootName n) s
  | .num n i => .num (rootName n) i

-- Remove KLR prefix from a name
def rmKLR : Name -> Name
  | .anonymous => .anonymous
  | .str n "KLR" => rmKLR n
  | .str n s => .str (rmKLR n) s
  | .num n i => .num (rmKLR n) i

-- Create a fully qualified identifier (e.g. _root_.KLR.foo)
def qualIdent (n : Name) (s : String) : Ident :=
  mkIdent (.str (rootName n) s)

-- Generate a qualified (function) name
def fnIdent (name : Name) (s : String) : Ident :=
  mkIdent (.str name s)

-- Generate a name suitable for an extern (C) symbol
def cIdent (name : Name) (s : String) : Ident :=
  let name := rmKLR name
  let cname := (name.toString ++ "_" ++ s).replace "." "_"
  mkIdent cname.toName

-- Make a list of parameter names, e.g.: x0, x1, ...
def makeNames (n : Nat) (s : String) : Array (TSyntax `ident) :=
  (Array.range n).map fun n => mkIdent (Name.mkStr1 s!"{s}{n}")

-- Get constructor parameter names, e.g: C : X -> Y -> Z  ===> x0, x1
def getParams (ctor : Name) : TermElabM (Array (TSyntax `ident)) := do
  let ci <- getConstInfoCtor ctor
  -- skip over implicit arguments
  let count <- forallTelescopeReducing ci.type fun xs _ => do
    let bis <- xs.mapM fun x => x.fvarId!.getBinderInfo
    pure $ bis.countP BinderInfo.isExplicit
  return makeNames count "x"

-- Get type parameter names, e.g: T a b  ===> a0, a1
def getTypeParams (name : Name) : TermElabM (Array (TSyntax `ident)) := do
  let tci <- getConstInfoInduct name
  return makeNames tci.numParams "a"

private def lit := Syntax.mkNatLit

-- Generate ToCBOR instances for a set of mutually recursive types
def mkToInstances (names : Array Name) : TermElabM (Array Command) := do
  let tags <- liftMetaM <| names.mapM serdeTags
  let mut cmds := #[]
  let mut insts := #[]
  for (name, typeTag, constTags) in names.zip tags do
    -- Generate match arms for each constructor
    let mut arms := #[]
    for (c, val) in constTags do
      let ps <- getParams c
      let arm <- `(matchAltExpr| | $(mkIdent c) $ps* => Id.run do
                     let arr := cborTag $(lit typeTag) $(lit val) $(lit ps.size)
                     $[let arr := arr ++ toCBOR $ps]*
                     pure arr)
      arms := arms.push arm

    -- Generate local instances for all type constructors
    -- They don'thave to be named, only in scope
    let ts <- getTypeParams name
    let ls := names.foldrM fun n body => `(
      let _ : ToCBOR ($(mkIdent n) $ts*) := ⟨$(fnIdent n "toBytes")⟩
      $body
    )
    -- combine local instances with body
    let body <- ls (<- `(match x with $arms:matchAlt*))

    -- Generate function for current type constructor
    let bs <- ts.mapM fun t => `(instBinder| [ToCBOR $t])
    let tname <- `( $(mkIdent name) $ts*)
    let cmd <- `(
      @[export $(cIdent name "toBytes")]
      partial def $(qualIdent name "toBytes") $bs:instBinder* (x : $tname) : ByteArray :=
      $body:term
    )
    cmds := cmds.push cmd

    -- Generate public instance declaration for current type constructor
    let inst <- `(
      instance $bs:instBinder* : ToCBOR $tname := ⟨ $(fnIdent name "toBytes") ⟩
    )
    insts := insts.push inst

  -- combine all functions into a mutual block
  -- return mutual block followed by public instance declarations
  return #[<- `(mutual $cmds* end)] ++ insts

def mkToCBOR (names : Array Name) : CommandElabM Bool := do
  let cmds <- liftTermElabM (mkToInstances names)
  cmds.forM elabCommand
  return true

initialize
  registerDerivingHandler ``ToCBOR mkToCBOR
