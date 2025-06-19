/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import TensorLib

open Lean(Command Expr Ident InductiveVal Name Syntax TSyntax Term getEnv isInductive mkIdent)
open Lean.Elab(registerDerivingHandler)
open Lean.Elab.Command(CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Deriving(Context Header mkContext mkHeader mkInstanceCmds)
open Lean.Elab.Term(TermElabM)
open Lean.Meta(mkListLit)
open Lean.Parser.Term(matchAltExpr)
open Lean.PrettyPrinter(ppCommand)
open TensorLib(Err impossible)

namespace KLR.Util

inductive Sexp where
| atom (s : String)
| list (es : List Sexp)
deriving BEq, Inhabited

namespace Sexp

class ToSexp (a : Type) where
  toSexp : a -> Sexp

export ToSexp(toSexp)

instance : ToSexp String where
  toSexp n := atom n

instance : ToSexp Int where
  toSexp n := atom (toString n)

instance : ToSexp Nat where
  toSexp n := toSexp (Int.ofNat n)

instance [ToSexp a] : ToSexp (List a) where
  toSexp e := list (e.map toSexp)

instance [ToSexp a] : ToSexp (Array a) where
  toSexp e := toSexp e.toList

instance [ToSexp a] [ToSexp b] : ToSexp (a × b) where
  toSexp p := list [toSexp p.1, toSexp p.2]

instance : ToSexp UInt8 where
  toSexp n := toSexp n.toNat

instance : ToSexp UInt16 where
  toSexp n := toSexp n.toNat

instance : ToSexp UInt32 where
  toSexp n := toSexp n.toNat

instance : ToSexp UInt64 where
  toSexp n := toSexp n.toNat

instance : ToSexp Int8 where
  toSexp n := toSexp n.toInt

instance : ToSexp Int16 where
  toSexp n := toSexp n.toInt

instance : ToSexp Int32 where
  toSexp n := toSexp n.toInt

instance : ToSexp Int64 where
  toSexp n := toSexp n.toInt

class FromSexp (a : Type) where
  fromSexp : Sexp -> Err a

def fromSexp (a : Type) [FromSexp a] (e : Sexp) : Err a :=
  FromSexp.fromSexp e

instance : FromSexp String where
  fromSexp s := do match s with
  | atom a => return a
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Int where
  fromSexp s := do match s with
  | atom a => match a.toInt? with
    | some n => return n
    | none => throw s!"Can't parse {a} as an Int"
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Nat where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toNat

instance : FromSexp UInt8 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt8

instance : FromSexp UInt16 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt16

instance : FromSexp UInt32 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt32

instance : FromSexp UInt64 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt64

instance : FromSexp Int8 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt8

instance : FromSexp Int16 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt16

instance : FromSexp Int32 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt32

instance : FromSexp Int64 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt64

private def nameToString : Name -> String
| .str _ s => s
| .anonymous => impossible "not expecting anonymous here"
| .num _ _ => impossible "not expecting a number here"

private def mkToSexpHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``ToSexp 1 indVal

private def mkToSexpStructureBody (header : Header) (e : Expr) : TermElabM Term := do
  let indName := e.getAppFn.constName!
  let fields := Lean.getStructureFieldsFlattened (<- getEnv) indName (includeSubobjectFields := false)
  let target := mkIdent header.targetNames[0]!
  let apps : Array Term <- fields.mapM fun f => ``(toSexp ($target).$(mkIdent f))
  let body : Term <- `(list [ $apps,* ])
  return body

private def mkToSexpStructureFunction (ctx : Context) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[0]!
  let header <- mkToSexpHeader ctx.typeInfos[0]!
  let binders := header.binders
  let type <- Lean.Elab.Term.elabTerm header.targetType none
  let body <- mkToSexpStructureBody header type
  `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Sexp := $body:term)

private def mkToSexpStructureInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "ToSexp" declName
  let cmds := #[<- mkToSexpStructureFunction ctx] ++ (<- mkInstanceCmds ctx ``ToSexp #[declName])
  return cmds

private def mkToSexpInductiveFunction (ctx : Context) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[0]!
  let indVal := ctx.typeInfos[0]!
  let header <- mkToSexpHeader indVal
  let mkToSexp (id : Ident) : TermElabM Term := do ``(toSexp $id:ident)

  let mut cases := #[]
  for ctor in indVal.ctors do
    let ctorInfo <- Lean.getConstInfoCtor ctor
    let n := ctorInfo.numFields
    let mut args : Array (TSyntax `term) := #[]
    let mut terms : Array (TSyntax `term) := #[]
    for _ in [0:n] do
      let a <- Lean.mkFreshUserName `a
      let a := mkIdent a
      let t : TSyntax `term <- mkToSexp a
      args := args.push a
      terms := terms.push t
    let ctorName := ctorInfo.name
    let stmt <- `(matchAltExpr| | $(mkIdent ctorName):ident $args:term* =>
      list ((atom $(Syntax.mkStrLit (nameToString ctorName))) :: [ $[$terms:term],* ] ))
    cases := cases.push stmt
  let type <- Lean.Elab.Term.elabTerm header.targetType none
  let indName := mkIdent type.getAppFn.constName!
  let a := mkIdent (← Lean.mkFreshUserName `a)
  `(private def $(mkIdent auxFunName):ident ($a : $indName) : Sexp :=
      match $a:ident with $cases:matchAlt*)

private def mkToSexpInductiveInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "ToSexp" declName
  let cmds := #[<- mkToSexpInductiveFunction ctx] ++ (<- mkInstanceCmds ctx ``ToSexp #[declName])
  return cmds

private def errMsg := "deriving ToSexp only works on single structures or inductives all of whose branches implement ToSexp"

private def mkToSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := match declNames with
| #[] => impossible "Expected a type"
| #[t] => do
  if (<- Lean.getConstInfoInduct t).all.length == 1 then
    -- single structure
    if (Lean.isStructure (<- getEnv) t) then
      let cmds <- liftTermElabM <| mkToSexpStructureInstance t
      cmds.forM fun (cmd:Command) => do
        elabCommand cmd
        -- SM: Leave this in
        -- dbg_trace (<- liftTermElabM <| ppCommand cmd)
      return true
    -- inductive where each branch is takes a single ToSexp argument
    else if (<- Lean.isInductive t) then
      let cmds <- liftTermElabM <| mkToSexpInductiveInstance t
      cmds.forM fun (cmd:Command) => do
        elabCommand cmd
        -- SM: Leave this in
        -- dbg_trace (<- liftTermElabM <| ppCommand cmd)
      return true
    else
      throwError errMsg
  else
    throwError errMsg
| _ => throwError errMsg

initialize
  registerDerivingHandler ``ToSexp mkToSexpInstanceHandler
