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
open Lean.Elab(registerDerivingHandler)
open Lean.Elab.Command(CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Deriving(Context Header mkContext mkHeader mkInstanceCmds)
open Lean.Elab.Term(TermElabM)
open TensorLib(impossible)

namespace KLR.Util

class FromBytes (a : Type) where
  fromBytesUnchecked : ByteArray -> Except String (a × ByteArray)

-- TODO: not sure how to use this yet from the macros
def fromBytes (a : Type) [H : Inhabited a] [NumBytes a] [FromBytes a] (arr : ByteArray) : Except String (a × ByteArray) :=
  if arr.size < numBytes H.default then throw "Not enough bytes" else FromBytes.fromBytesUnchecked arr

namespace FromBytes

instance : FromBytes UInt8 where
  fromBytesUnchecked arr := return (arr[0]!, arr.drop 1)

instance : FromBytes UInt16 where
  fromBytesUnchecked arr := return ((arr.take 2).toUInt16LE!, arr.drop 2)

instance : FromBytes UInt32 where
  fromBytesUnchecked arr := return ((arr.take 4).toUInt32LE!, arr.drop 4)

instance : FromBytes UInt64 where
  fromBytesUnchecked arr := return ((arr.take 8).toUInt64LE!, arr.drop 8)

instance : FromBytes Int8 where
  fromBytesUnchecked arr := return (arr[0]!.toInt8, arr.drop 1)

instance : FromBytes Int16 where
  fromBytesUnchecked arr := return ((arr.take 2).toUInt16LE!.toInt16, arr.drop 2)

instance : FromBytes Int32 where
  fromBytesUnchecked arr := return ((arr.take 4).toUInt32LE!.toInt32, arr.drop 4)

instance : FromBytes Int64 where
  fromBytesUnchecked arr := return ((arr.take 8).toUInt64LE!.toInt64, arr.drop 8)

instance : FromBytes Float32 where
  fromBytesUnchecked arr := return (Float32.ofBits (arr.take 4).toUInt32LE!, arr.drop 4)

instance : FromBytes Float where
  fromBytesUnchecked arr := return (Float.ofBits (arr.take 8).toUInt64LE!, arr.drop 8)

instance [Enum a] : FromBytes a where
  fromBytesUnchecked arr := (Enum.fromUInt8 arr[0]!).map fun e => (e, arr.drop 1)

instance : FromBytes (BitVec n) where
  fromBytesUnchecked arr :=
    let k := (n + 7) / 8
    return ((arr.take k).toBitVecLE n, arr.drop k)

end FromBytes

def mkFromBytesHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``FromBytes 1 indVal

def mkFromBytesBody (e : Expr): TermElabM Term := do
  let indName := e.getAppFn.constName!
  let env <- getEnv
  let str := Lean.getStructureInfo env indName
  let fields := str.fieldNames
  -- let fields := Lean.getStructureFieldsFlattened env indName (includeSubobjectFields := false)
  let args := fields.map mkIdent
  -- Trying to use the class name didn't work. We just hope that `mk` on its own works
  -- let mut body <- `(return ($(mkIdent indName).mk $args*, arr))
  let mut body <- `(return (.mk $args*, arr))
  for field in fields.reverse do
    body <- `((FromBytes.fromBytesUnchecked arr).bind fun ($(mkIdent field), arr) => $body)
  body <- `(fun arr => $body)
  return body

def mkFromBytesFunction (ctx : Context) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[0]!
  let header     ←  mkFromBytesHeader ctx.typeInfos[0]!
  let binders    := header.binders
  Lean.Elab.Term.elabBinders binders fun _ => do
  let type       ← Lean.Elab.Term.elabTerm header.targetType none
  let body   ← mkFromBytesBody type
  let indName := mkIdent type.getAppFn.constName!
  `(private def $(mkIdent auxFunName):ident : ByteArray -> Except String ($indName × ByteArray) := $body:term)

private def mkFromBytesInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "FromBytes" declName
  let cmds := #[← mkFromBytesFunction ctx] ++ (← mkInstanceCmds ctx ``FromBytes #[declName])
  return cmds

private def errMsg := "deriving FromBytes only works on single structures"

def mkFromBytesInstanceHandler (declNames : Array Name) : CommandElabM Bool := match declNames with
| #[] => impossible "Expected a type"
| #[t] => do
  if (Lean.isStructure (<- getEnv) t) && (<- Lean.getConstInfoInduct t).all.length == 1 then
    let cmds ← liftTermElabM <| mkFromBytesInstance t
    cmds.forM elabCommand
    return true
  else
    throwError errMsg
    return false
| _ => throwError errMsg

initialize
  registerDerivingHandler ``FromBytes mkFromBytesInstanceHandler

end KLR.Util
