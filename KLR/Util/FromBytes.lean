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
open TensorLib(Err impossible)

namespace KLR.Util

class FromBytes (a : Type) where
  fromBytesUnchecked : ByteArray -> Except String (a × ByteArray)

def fromBytes (a : Type) [H : Inhabited a] [NumBytes a] [FromBytes a] (arr : ByteArray) : Err (a × ByteArray) :=
  if arr.size < numBytes H.default then throw "Not enough bytes" else FromBytes.fromBytesUnchecked arr

namespace FromBytes

-- Ensure we consume the entire input
def fromBytes' (a : Type) [H : Inhabited a] [NumBytes a] [FromBytes a] (arr : ByteArray) : Err a := do
  let (x, arr) <- fromBytes a arr
  if arr.size != 0 then throw "Unconsumed bytes" else return x

-- Keep consuming until the input is exhausted
def array (a : Type) [Inhabited a] [NumBytes a] [FromBytes a] (arr : ByteArray) : Err (Array a) := do
  let size := numBytes (default:a)
  if arr.size % size != 0 then throw "Array size not a multiple of element size" else
  let mut res := #[]
  let mut arr := arr
  for _ in [0:arr.size / size] do
    let (x, arr') <- fromBytes a arr
    arr := arr'
    res := res.push x
  return res

instance : FromBytes UInt8 where
  fromBytesUnchecked arr := return (arr[0]!, arr.drop 1)

instance : FromBytes UInt16 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 2
    return (l.toUInt16LE!, r)

instance : FromBytes UInt32 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 4
    return (l.toUInt32LE!, r)

instance : FromBytes UInt64 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 8
    return (l.toUInt64LE!, r)

instance : FromBytes Int8 where
  fromBytesUnchecked arr := return (arr[0]!.toInt8, arr.drop 1)

instance : FromBytes Int16 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 2
    return (l.toInt16LE!, r)

instance : FromBytes Int32 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 4
    return (l.toInt32LE!, r)

instance : FromBytes Int64 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 8
    return (l.toInt64LE!, r)

instance : FromBytes Float32 where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 4
    return (Float32.ofBits l.toUInt32LE!, r)

instance : FromBytes Float where
  fromBytesUnchecked arr :=
    let (l, r) := arr.splitAt 8
    return (Float.ofBits l.toUInt64LE!, r)

instance [Enum a] : FromBytes a where
  fromBytesUnchecked arr := (Enum.fromUInt8 arr[0]!).map fun e => (e, arr.drop 1)

instance : FromBytes (BitVec n) where
  fromBytesUnchecked arr :=
    let k := (n + 7) / 8
    let (l, r) := arr.splitAt k
    return (l.toBitVecLE n, r)

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
