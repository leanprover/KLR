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

/-! # AccessPattern → AP lowering pass -/

namespace KLR.Core

/-- Function to convert an Access to an AccessPattern.
Note: This lowering does not work in all cases, for example, if the Access in an AccessBasic whose
Par dimension takes steps that are not equal to 1. Returns a None in this case. -/
def Access.lowerAccessPattern (a : Access) : KLR.Err AccessPattern := do
  -- The layout of a tensor in memory
  -- Note that because accesses are values, we have are forced to assume that all tensors are
  -- laid out in row major form.
  let layout := Layout.rowMajorForm (← a.shape)
  -- The par dimension of the access must start at zero and have step 1
  let ap := a.interpPar
  if ap.start ≠ 0 then .error "Cannot lower AccessPatterns with nonzero starting location. " else
  if ap.step ≠ 1  then .error "Cannot lower AccessPatterns with step not equal to 1. " else
  return CompileIndex.freePairs a.tensor ap.num layout

def Value.lowerAccessPatterns : Value → KLR.Err Value
| .access a => do return .access <| .pattern (← a.lowerAccessPattern)
| x => .ok x

def Keyword.lowerAccessPatterns (k : Keyword) : KLR.Err Keyword := do
  return { k with value := (← k.value.lowerAccessPatterns) }

def Expr.lowerAccessPatterns : Expr → KLR.Err Expr
| .value v => do return .value (← v.lowerAccessPatterns)
| .call f args kwargs => do
  let args' ← args.mapM Value.lowerAccessPatterns
  return .call f args' kwargs

def TensorRef.lowerAccessPatterns : TensorRef → KLR.Err TensorRef
| .abstract a => do return .abstract <| .pattern (← a.lowerAccessPattern)
| x => do return x

-- TODO: Is there a way to make this less horrible with metaprogramming? All argumetns are of different types.
def Operator.lowerAccessPatterns (k : Operator) : KLR.Err Operator :=
  match k with
  | .activate           op => do return .activate           { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .affineSelect       op => do return .affineSelect       { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .batchNormAggregate op => do return .batchNormAggregate { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .batchNormStats     op => do return .batchNormStats     { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .copy               op => do return .copy               { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .copyPredicated     op => do return .copyPredicated     { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), predicate := (← op.predicate.lowerAccessPatterns) }
  | .dmaCopy            op => do return .dmaCopy            { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .dmaTranspose       op => do return .dmaTranspose       { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .dropout            op => do return .dropout            { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .findIndex8         op => do return .findIndex8         { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .iota               op => do return .iota               { op with dst := (← op.dst.lowerAccessPatterns)}
  | .loadMaskRegister   op => do return .loadMaskRegister   op
  | .loadStationary     op => do return .loadStationary     { op with src := (← op.src.lowerAccessPatterns) }
  | .localGather        op => do return .localGather        { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .matMul             op => do return .matMul             { op with dst := (← op.dst.lowerAccessPatterns), moving := (← op.moving.lowerAccessPatterns) }
  | .matchReplace8      op => do return .matchReplace8      { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .matchValueLoad     op => do return .matchValueLoad     { op with src := (← op.src.lowerAccessPatterns) }
  | .max8               op => do return .max8               { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .memSet             op => do return .memSet             { op with dst := (← op.dst.lowerAccessPatterns) }
  | .rangeSelect        op => do return .rangeSelect        { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .reciprocal         op => do return .reciprocal         { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .scalarTensorTensor op => do return .scalarTensorTensor { op with dst := (← op.dst.lowerAccessPatterns), src0 := (← op.src0.lowerAccessPatterns), src1 := (← op.src1.lowerAccessPatterns) }
  | .shuffle            op => do return .shuffle            { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .tensorReduce       op => do return .tensorReduce       { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .tensorTensorScan   op => do return .tensorTensorScan   { op with dst := (← op.dst.lowerAccessPatterns), src0 := (← op.src0.lowerAccessPatterns), src1 := (← op.src1.lowerAccessPatterns) }
  | .transpose          op => do return .transpose          { op with src := (← op.src.lowerAccessPatterns) }
  -- Above are all of the cases, but for some reason,
  -- I get a timeout when I don't include a default case.
  | _ => .error "Unreachable"

def Stmt.lowerAccessPatterns : Stmt → KLR.Err Stmt
  | .oper op => return .oper (<- op.lowerAccessPatterns)
  | s => return s

def lowerAccessPatterns (k : Kernel) : KLR.Err Kernel := do
  let body' ← k.body.mapM Stmt.lowerAccessPatterns
  return { k with body := body'}
