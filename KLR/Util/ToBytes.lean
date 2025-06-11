/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import Util.Enum
import Util.NumBytes
import TensorLib.ByteArray
import TensorLib.Bytes

open Lean(Command Expr InductiveVal Name Term getEnv isInductive mkIdent)
open Lean.Parser.Term(matchAltExpr)
open Lean.PrettyPrinter(ppCommand)
open Lean.Elab(registerDerivingHandler)
open Lean.Elab.Command(CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Deriving(Context Header mkContext mkHeader mkInstanceCmds)
open Lean.Elab.Term(TermElabM)
open TensorLib(ToBEByteArray ToLEByteArray impossible toBEByteArray toLEByteArray)

namespace KLR.Util

private def combine (xs : Array ByteArray) : ByteArray := Id.run do
  let n := (xs.map fun x => x.size).sum
  let mut arr := ByteArray.emptyWithCapacity n
  for x in xs do
    arr := arr.append x
  arr

#guard combine #[⟨ #[0,1,2,3] ⟩, ⟨ #[3,2,1,0] ⟩] == ⟨ #[0,1,2,3,3,2,1,0] ⟩

class ToBytes (a : Type) where
  toBytes : a -> ByteArray

export ToBytes(toBytes)

namespace ToBytes

-- Not sure how to use this yet, since generating monadic code seems harder
def toBytesChecked [NumBytes a][ToBytes a] (x : a) : Except String ByteArray :=
  let arr := toBytes x
  let expected := numBytes x
  if arr.size == expected then return arr
  else throw s!"Expected {expected} bytes, got {arr.size}"

instance [ToLEByteArray a] : ToBytes a where
  toBytes := toLEByteArray

instance [Enum a] : ToBytes a where
  toBytes x := toBytes (Enum.toUInt8 x)

instance [ToBytes a] : ToBytes (Array a) where
  toBytes xs := combine (xs.map toBytes)

instance [ToBytes a] : ToBytes (List a) where
  toBytes xs := toBytes xs.toArray

instance [ToBytes a][ToBytes b] : ToBytes (a × b) where
  toBytes := fun (x, y) => combine #[toBytes x, toBytes y]

end ToBytes

def mkToBytesHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``ToBytes 1 indVal

def mkToBytesStructureBody (header : Header) (e : Expr) : TermElabM Term := do
  let indName := e.getAppFn.constName!
  let fields := Lean.getStructureFieldsFlattened (<- getEnv) indName (includeSubobjectFields := false)
  let target := mkIdent header.targetNames[0]!
  let apps : Array Term <- fields.mapM fun f => ``(ToBytes.toBytes ($target).$(mkIdent f))
  let body : Term <- `(combine #[ $apps,* ])
  return body

def mkToBytesStructureFunction (ctx : Context) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[0]!
  let header <- mkToBytesHeader ctx.typeInfos[0]!
  let binders := header.binders
  let type <- Lean.Elab.Term.elabTerm header.targetType none
  let body <- mkToBytesStructureBody header type
  `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : ByteArray := $body:term)

private def mkToBytesStructureInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "toBytes" declName
  let cmds := #[<- mkToBytesStructureFunction ctx] ++ (<- mkInstanceCmds ctx ``ToBytes #[declName])
  return cmds

def mkToBytesInductiveFunction (ctx : Context) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[0]!
  let indVal := ctx.typeInfos[0]!
  let header <- mkToBytesHeader indVal
  let mut cases /- : Array matchAltExpr -/ := #[]
  for ctor in indVal.ctors do
    let ctorInfo <- Lean.getConstInfoCtor ctor
    let a := mkIdent (<- Lean.mkFreshUserName `a)
    let stmt <- `(matchAltExpr| | $(mkIdent ctorInfo.name):ident $a:term => toBytes $a)
    cases := cases.push stmt
  let type <- Lean.Elab.Term.elabTerm header.targetType none
  let indName := mkIdent type.getAppFn.constName!
  let a := mkIdent (← Lean.mkFreshUserName `a)
  `(private def $(mkIdent auxFunName):ident ($a : $indName) : ByteArray :=
      match $a:ident with $cases:matchAlt*)

private def mkToBytesInductiveInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "toBytes" declName
  let cmds := #[<- mkToBytesInductiveFunction ctx] ++ (<- mkInstanceCmds ctx ``ToBytes #[declName])
  return cmds

private def errMsg := "deriving ToBytes only works on single structures or inductives all of whose branches have a single ToBytes argument"

def mkToBytesInstanceHandler (declNames : Array Name) : CommandElabM Bool := match declNames with
| #[] => impossible "Expected a type"
| #[t] => do
  if (<- Lean.getConstInfoInduct t).all.length == 1 then
    -- single structure
    if (Lean.isStructure (<- getEnv) t) then
      let cmds <- liftTermElabM <| mkToBytesStructureInstance t
      cmds.forM fun (cmd:Command) => do
        elabCommand cmd
        -- SM: Leave this in
        -- dbg_trace (<- liftTermElabM <| ppCommand cmd)
      return true
    -- inductive where each branch is takes a single ToBytes argument
    else if (<- Lean.isInductive t) then
      let cmds <- liftTermElabM <| mkToBytesInductiveInstance t
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
  registerDerivingHandler ``ToBytes mkToBytesInstanceHandler

end KLR.Util
