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

namespace KLR.Core

abbrev NameMap := List (String × String)

def mkNameMap (outputs : List TensorName) : NameMap :=
  outputs.mapIdx fun idx tn => (tn.name, s!"output_{idx}")

def renameStr (m : NameMap) (s : String) : String :=
  m.find? (·.1 == s) |>.map (·.2) |>.getD s

def renameTensor (m : NameMap) (t : TensorName) : Err TensorName :=
  let newName := renameStr m t.name
  let newAddr := { t.address with name := renameStr m t.address.name }
  TensorName.make newName t.dtype t.shape (some newAddr) t.addressRotation

partial def renameAccess (m : NameMap) : Access → Err Access
  | .simple t => return .simple (← renameTensor m t)
  | .basic b => do
    let t ← renameTensor m b.tensor
    AccessBasic.make t b.indexes >>= (return .basic ·)
  | .pattern p => return .pattern { p with tensor := ← renameTensor m p.tensor }
  | .birPattern b => do
    let t ← renameTensor m b.tensor
    let so ← match b.scalarOffset with
      | some (.acc a) => pure $ some (.acc (← renameAccess m a))
      | some (.reg r) => pure $ some (.reg r)
      | none => pure none
    let vo ← b.vectorOffset.mapM (renameAccess m)
    return .birPattern { b with tensor := t, scalarOffset := so, vectorOffset := vo }

def renameTensorRef (m : NameMap) : TensorRef → Err TensorRef
  | .abstract a => return .abstract (← renameAccess m a)
  | other => return other

def renameOperand (m : NameMap) : Operand → Err Operand
  | .tile t => return .tile (← renameTensorRef m t)
  | other => return other

def renameOperator (m : NameMap) (op : Operator) : Err Operator :=
  MapTensorRefs.mapM (renameTensorRef m) (renameOperand m) op

def renameStmt (m : NameMap) : Stmt → Err Stmt
  | .oper op name pos => return .oper (← renameOperator m op) name pos

def renameBlock (m : NameMap) (b : Block) : Err Block := do
  return { b with body := ← b.body.mapM (renameStmt m) }

def canonicalizeOutputs (k : LncKernel) : Err LncKernel := do
  let m := mkNameMap k.outputs
  let outputs ← k.outputs.mapIdxM fun idx tn =>
    TensorName.make s!"output_{idx}" tn.dtype tn.shape
      (some { tn.address with name := s!"output_{idx}" }) tn.addressRotation
  let bodies ← k.bodies.mapM (·.mapM (renameBlock m))
  return { k with outputs, bodies }
