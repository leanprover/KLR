/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import KLR.Serde.Attr
import KLR.Serde.Basic
import Lean

/-
# ToCBOR and FromCBOR deriving
-/

namespace KLR.Serde.Elab
open Lean Parser.Term Meta Elab Command Deriving
open PrettyPrinter

-- Generate a absolute path for a name
private def rootName : Name -> Name
  | .anonymous => .str .anonymous "_root_"
  | .str n s => .str (rootName n) s
  | .num n i => .num (rootName n) i

-- Remove KLR prefix from a name
private def rmKLR : Name -> Name
  | .anonymous => .anonymous
  | .str n "KLR" => rmKLR n
  | .str n s => .str (rmKLR n) s
  | .num n i => .num (rmKLR n) i

-- Create a fully qualified identifier (e.g. _root_.KLR.foo)
private def qualIdent (n : Name) (s : String) : Ident :=
  mkIdent (.str (rootName n) s)

-- Generate a qualified (function) name
private def fnIdent (name : Name) (s : String) : Ident :=
  mkIdent (.str name s)

-- Generate a name suitable for an extern (C) symbol
private def cIdent (name : Name) (s : String) : Ident :=
  let name := rmKLR name
  let cname := name.toString ++ "_" ++ s
  let cname := cname.replace "." "_"
  let cname := cname.replace "'" "_"
  mkIdent cname.toName

-- Make a list of parameter names, e.g.: x0, x1, ...
private def makeNames (n : Nat) (s : String) : Array (TSyntax `ident) :=
  (Array.range n).map fun n => mkIdent (Name.mkStr1 s!"{s}{n}")

-- Get constructor parameter names, e.g: C : X -> Y -> Z  ===> x0, x1
private def getParams (ctor : Name) : TermElabM (Array (TSyntax `ident)) := do
  let ci <- getConstInfoCtor ctor
  -- skip over implicit arguments
  let count <- forallTelescopeReducing ci.type fun xs _ => do
    let bis <- xs.mapM fun x => x.fvarId!.getBinderInfo
    pure $ bis.countP BinderInfo.isExplicit
  return makeNames count "x"

-- Get type parameter names, e.g: T a b  ===> a0, a1
private def getTypeParams (name : Name) : TermElabM (Array (TSyntax `ident)) := do
  let tci <- getConstInfoInduct name
  return makeNames tci.numParams "a"

private def lit := Syntax.mkNatLit

-- Generate ToCBOR instances for a set of mutually recursive types
private def mkToInstances (names : Array Name) : TermElabM (Array Command) := do
  let tags <- liftMetaM <| names.mapM serdeTags
  let mut cmds := #[]
  let mut insts := #[]
  for (name, typeTag, constTags) in names.zip tags do
    -- Generate match arms for each constructor
    let mut arms := #[]
    let mut armsIO := #[]
    for (c, val) in constTags do
      let ps <- getParams c
      let arm <- `(matchAltExpr| | $(mkIdent c) $ps* => Id.run do
                     let arr := cborTag $(lit typeTag) $(lit val) $(lit ps.size)
                     $[let arr := arr ++ toCBOR $ps]*
                     pure arr)
      arms := arms.push arm
      let armIO <- `(matchAltExpr| | $(mkIdent c) $ps* => do
                       let arr := cborTag $(lit typeTag) $(lit val) $(lit ps.size)
                       h.write arr
                       $[writeCBOR h $ps]*)
      armsIO := armsIO.push armIO

    -- Generate local instances for all type constructors
    -- They don't have to be named, only in scope
    let ts <- getTypeParams name
    let ls := names.foldrM fun n body => `(
      let _ : ToCBOR ($(mkIdent n) $ts*) :=
        ⟨$(fnIdent n "toBytes"), $(fnIdent n "writeBytes")⟩
      $body
    )
    -- combine local instances with body
    let body <- ls (<- `(match x with $arms:matchAlt*))
    let bodyIO <- ls (<- `(match x with $armsIO:matchAlt*))

    -- Generate functions for current type constructor
    let bs <- ts.mapM fun t => `(instBinder| [ToCBOR $t])
    let tname <- `( $(mkIdent name) $ts*)
    let cmd <- `(
      @[export $(cIdent name "toBytes")]
      partial def $(qualIdent name "toBytes") $bs:instBinder* (x : $tname) : ByteArray :=
      $body:term
    )
    cmds := cmds.push cmd
    let cmd <- `(
      @[export $(cIdent name "writeBytes")]
      partial def $(qualIdent name "writeBytes") $bs:instBinder* (h : IO.FS.Handle) (x : $tname) : IO Unit :=
      $bodyIO:term
    )
    cmds := cmds.push cmd

    -- Generate public instance declaration for current type constructor
    let inst <- `(
      instance $bs:instBinder* : ToCBOR $tname :=
        ⟨ $(fnIdent name "toBytes"), $(fnIdent name "writeBytes") ⟩
    )
    insts := insts.push inst

  -- combine all functions into a mutual block
  -- return mutual block followed by public instance declarations
  return #[<- `(mutual $cmds* end)] ++ insts

-- Generate FromCBOR instances for a set of mutually recursive types
private def mkFromInstances (names : Array Name) : TermElabM (Array Command) := do
  let tags <- liftMetaM <| names.mapM serdeTags
  let mut cmds := #[]
  let mut insts := #[]
  for (name, typeTag, constTags) in names.zip tags do
    -- Generate match arms for each constructor
    let mut arms := #[]
    for (c, val) in constTags do
      let ps <- getParams c
      -- 4 because parseCBORTag consumes 4 bytes
      let arm <- `(matchAltExpr| | $(lit val) => do
                     let sz := 4
                     $[let (arr, sz, $ps) <- KLR.Serde.parseCBOR' arr sz]*
                     return (sz, $(mkIdent c) $ps*))
      arms := arms.push arm

    -- Build match expression
    let cases <- `(match vt with
      $arms:matchAlt*
      | _ => throw s!"unexpected value tag {vt}")

    -- Generate local instances for all type constructors
    -- They don't have to be named, only in scope
    let ts <- getTypeParams name
    let ls := names.foldrM fun n body => `(
      let _ : FromCBOR ($(mkIdent n) $ts*) := ⟨$(fnIdent n "fromBytes")⟩
      $body
    )

    -- combine local instances with body
    let body <- ls (<- `(do
      let (tt, vt, sz, arr) <- parseCBORTag arr
      if tt != $(lit typeTag) then
        throw s!"unexpected type tag {tt}"
      $cases:term))

    -- Generate function for current type constructor
    let bs <- ts.mapM fun t => `(instBinder| [FromCBOR $t])
    let tname <- `( $(mkIdent name) $ts*)
    let cmd <- `(
      @[export $(cIdent name "fromBytes")]
      partial def $(qualIdent name "fromBytes") $bs:instBinder* (arr : ByteArray) : Err (Nat × $tname) := do
      $body:term
    )
    --logWarning (<- ppCommand cmd)
    cmds := cmds.push cmd

    -- Generate public instance declaration for current type constructor
    let inst <- `(
      instance $bs:instBinder* : FromCBOR $tname := ⟨ $(fnIdent name "fromBytes") ⟩
    )
    insts := insts.push inst

  -- combine all functions into a mutual block
  -- return mutual block followed by public instance declarations
  return #[<- `(mutual $cmds* end)] ++ insts

def mkToCBOR (names : Array Name) : CommandElabM Bool := do
  let cmds <- liftTermElabM (mkToInstances names)
  cmds.forM elabCommand
  return true

def mkFromCBOR (names : Array Name) : CommandElabM Bool := do
  let cmds <- liftTermElabM (mkFromInstances names)
  cmds.forM elabCommand
  return true

initialize
  registerDerivingHandler ``ToCBOR mkToCBOR
  registerDerivingHandler ``FromCBOR mkFromCBOR
