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

import KLR.Core.Basic
import KLR.Compile.Pass

namespace KLR.Core

abbrev NameMap := List (String × String)

structure State where
  nameMap : NameMap := []
  addrNameMap : NameMap := []

open KLR.Compile.Pass in

abbrev CanonicalizeOutputs (α : Type) := Pass State α

def findCommonName (names : List String) (idx : Nat) : String :=
  match names.filter (!·.isEmpty) with
  | [] => s!"output_{idx}"
  | [n] => n
  | n :: ns =>
    let common := ns.foldl (fun a b => (a.toSubstring.commonPrefix b.toSubstring).toString) n
    if common.isEmpty then s!"output_{idx}"
    else
      let trimmed := if common.endsWith "." then common.dropRight 1 else common
      trimmed

def mkNameMap (outputs : List (List TensorName)) : CanonicalizeOutputs (NameMap × NameMap) := do
  let result ← outputs.mapIdxM fun idx tns => do
    let names := tns.map (·.name)
    let addrNames := tns.map (·.address.name)
    -- If all names are the same, keep the original name (no renaming needed)
    let common ← if names.eraseDups.length == 1 then
        pure names.head!
      else do
        let commonStr := findCommonName names idx
        pure (← KLR.Compile.Pass.freshName commonStr.toName).toString
    let addrCommon ← if addrNames.eraseDups.length == 1 then
        pure addrNames.head!
      else do
        let addrCommonStr := findCommonName addrNames idx
        pure (← KLR.Compile.Pass.freshName addrCommonStr.toName).toString
    let nameEntries := names.map (·, common)
    let addrEntries := addrNames.map (·, addrCommon)
    return (nameEntries, addrEntries)
  return (List.flatten (result.map (·.1)), List.flatten (result.map (·.2)))

def renameStr (nameMap : NameMap) (s : String) : String :=
  nameMap.find? (·.1 == s) |>.map (·.2) |>.getD s

def renameTensor (t : TensorName) : CanonicalizeOutputs TensorName := do
  let newName := renameStr ((← get).nameMap) t.name
  let newAddrName := renameStr ((← get).addrNameMap) t.address.name
  let newAddr := { t.address with name := newAddrName }
  TensorName.make newName t.dtype t.shape (some newAddr) t.addressRotation

partial def renameAccess : Access → CanonicalizeOutputs Access
  | .simple t => return .simple (← renameTensor t)
  | .basic b => do
    let t ← renameTensor b.tensor
    AccessBasic.make t b.indexes >>= (return .basic ·)
  | .pattern p => return .pattern { p with tensor := ← renameTensor p.tensor }
  | .birPattern b => do
    let t ← renameTensor b.tensor
    let so ← match b.scalarOffset with
      | some (.acc a) => pure $ some (.acc (← renameAccess a))
      | some (.reg r) => pure $ some (.reg r)
      | none => pure none
    let vo ← b.vectorOffset.mapM renameAccess
    return .birPattern { b with tensor := t, scalarOffset := so, vectorOffset := vo }

def renameTensorRef : TensorRef → CanonicalizeOutputs TensorRef
  | .abstract a => return .abstract (← renameAccess a)
  | other => return other

def renameOperand : Operand → CanonicalizeOutputs Operand
  | .tile t => return .tile (← renameTensorRef t)
  | other => return other

def renameOperator (op : Operator) : CanonicalizeOutputs Operator :=
  MapTensorRefs.mapM renameTensorRef renameOperand op

def renameStmt : Stmt → CanonicalizeOutputs Stmt
  | .oper op name pos => return .oper (← renameOperator op) name pos

def renameBlock (b : Block) : CanonicalizeOutputs Block := do
  return { b with body := ← b.body.mapM renameStmt }

def canonicalizeOutputs (k : LncKernel) (outputNames : List (List Core.TensorName)) : CanonicalizeOutputs LncKernel := do
  let sharedNames := k.sharedBuffers.map (·.name)
  let (m, am) ← mkNameMap outputNames
  modify fun s => { s with nameMap := m, addrNameMap := am }
  let outputs ← k.outputs.mapM fun tn =>
    if sharedNames.contains tn.name then
      pure tn
    else do
      let newName := renameStr ((<-get).nameMap) tn.name
      let newAddrName := renameStr ((<-get).addrNameMap) tn.address.name
      let newAddr := { tn.address with name := newAddrName }
      TensorName.make newName tn.dtype tn.shape (some newAddr) tn.addressRotation
  let bodies ← k.bodies.mapM (·.mapM renameBlock)
  return { k with outputs, bodies }
