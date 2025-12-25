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
import KLR.Core.Indexing
import KLR.Core.Operators

/-! # AccessPattern → AP lowering pass -/

namespace KLR.Core

structure LowerAPState where
  unsafeCast := false

instance : Inhabited LowerAPState where
  default := {}

/-- LowerAP monad for access pattern lowering -/
abbrev LowerAP := StateT LowerAPState KLR.Err

/-- Function to convert an Access to an AccessPattern.
Note: This lowering does not work in all cases, for example, if the Access in an AccessBasic whose
Par dimension takes steps that are not equal to 1. Returns a None in this case. -/
def Access.lowerAccessPattern (a : Access) : LowerAP BirAccessPattern := do
  -- Don't violate invariants of proved code
  if let .birPattern b := a then
    return b

  -- The layout of a tensor in memory
  -- Note that because accesses are values, we have are forced to assume that all tensors are
  -- laid out in row major form.
  let ap <- Access.toAP a
  if ap.tensor.address.memory != .hbm then
    if ap.parOffset ∉ [0, 32, 64, 96] then
      throw s!"Invalid partition start offset {ap.freeOffset} for non-HBM memory. Valid offsets are: 0, 32, 64, 96"
  let birAp := BirAccessPattern.fromAccessPattern ap
  let state ← get
  if state.unsafeCast && birAp.tensor.dtype == Core.Dtype.float8_e4m3fn then
    if freeWF: birAp.tensor.shape.freeElements * Core.Dtype.float8_e4m3.size <=
               birAp.tensor.address.freeSize then
      return { birAp with tensor :=
        { birAp.tensor with dtype := Core.Dtype.float8_e4m3, freeWF } }
    else
      throw "float8_e4m3 is too large to cast from {birAp.tensor.dtype}"
  return birAp

def TensorRef.lowerAccessPatterns : TensorRef → LowerAP TensorRef
| .abstract a => do return .abstract <| .birPattern (← a.lowerAccessPattern)
| x => do return x

def Operand.lowerAccessPatterns : Operand -> LowerAP Operand
  | .tile t => do return .tile (<- t.lowerAccessPatterns)
  | x => return x

def Operator.lowerAccessPatterns (op : Operator) : LowerAP Operator :=
  MapTensorRefs.mapM TensorRef.lowerAccessPatterns Operand.lowerAccessPatterns op

def Stmt.lowerAccessPatterns : Stmt → LowerAP Stmt
  | .oper op name pos => return .oper (<- op.lowerAccessPatterns) name pos

def Block.lowerAccessPatterns (b : Block) : LowerAP Block := do
  let body <- b.body.mapM Stmt.lowerAccessPatterns
  return { b with body := body }

def Kernel.lowerAccessPatterns (k : Kernel) : LowerAP Kernel := do
  let body' ← k.body.mapM Block.lowerAccessPatterns
  return { k with body := body'}

def lowerAccessPatterns (k : LncKernel) : LowerAP LncKernel := do
  let mut bodies := []
  for body in k.bodies do
    let body' ← body.mapM Block.lowerAccessPatterns
    bodies := body' :: bodies
  return { k with bodies := bodies.reverse }
