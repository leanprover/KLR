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

import KLR.Compile.Pass
import KLR.NKI.Basic
import KLR.Python
import KLR.Util

/-
Simplification pass: convert operators to the ones that don't use mutating assignment
-/

namespace KLR.NKI
open Compile.Pass

abbrev SimplifyOp := PassM

-- TODO: maybe we can fetch these names from the NKI environment in Trace/NKI.lean?
private def operatorNames : List Name := [
  `neuronxcc.nki.isa.nc_matmul,
  `neuronxcc.nki.isa.nc_transpose,
  `neuronxcc.nki.isa.activation,
  `neuronxcc.nki.isa.activation_reduce,
  `neuronxcc.nki.isa.tensor_reduce,
  `neuronxcc.nki.isa.tensor_partition_reduce,
  `neuronxcc.nki.isa.tensor_tensor,
  `neuronxcc.nki.isa.tensor_tensor_scan,
  `neuronxcc.nki.isa.scalar_tensor_tensor,
  `neuronxcc.nki.isa.tensor_scalar,
  `neuronxcc.nki.isa.tensor_scalar_reduce,
  `neuronxcc.nki.isa.tensor_copy,
  `neuronxcc.nki.isa.tensor_copy_dynamic_src,
  `neuronxcc.nki.isa.tensor_copy_dynamic_dst,
  `neuronxcc.nki.isa.tensor_copy_predicated,
  `neuronxcc.nki.isa.reciprocal,
  `neuronxcc.nki.isa.iota,
  `neuronxcc.nki.isa.dropout,
  `neuronxcc.nki.isa.affine_select,
  `neuronxcc.nki.isa.range_select,
  `neuronxcc.nki.isa.memset,
  `neuronxcc.nki.isa.bn_stats,
  `neuronxcc.nki.isa.bn_aggr,
  `neuronxcc.nki.isa.local_gather,
  `neuronxcc.nki.isa.dma_copy,
  `neuronxcc.nki.isa.max8,
  `neuronxcc.nki.isa.nc_find_index8,
  `neuronxcc.nki.isa.nc_match_replace8,
  `neuronxcc.nki.isa.nc_stream_shuffle
]

private def rewriteOp (rhs: Expr) (dst: Expr) : SimplifyOp (Option Stmt') := do
  match rhs.expr with
  | .call f args kws =>
    if let .var n := f.expr then
      if operatorNames.contains n then
        if kws.any fun x => x.name == "dst" then
          throw  "Operation with destination specified should not use assignment form"
        let kws : List Keyword := ⟨ "dst",  dst⟩ :: kws
        let call : Expr' := .call f args kws
        return some (.expr ⟨call, rhs.pos⟩)
      else
        return none
    else
      return none
  | _ => none

mutual
private def stmt (s : Stmt) : SimplifyOp (Stmt) := do
  return ⟨ <- stmt' s.stmt, s.pos ⟩
  termination_by sizeOf s
  decreasing_by cases s; simp; omega

private def stmts (s : List Stmt) : SimplifyOp (List Stmt) := do
  return <- s.mapM stmt
  termination_by sizeOf s

private def stmt' (s : Stmt') : SimplifyOp Stmt' := do
  match s with
  | .letM p ty e =>
    let (n, _) <- Pattern.findVar [p]
    match <- rewriteOp e ⟨ .var n, e.pos ⟩ with
    | some _ => throw "assignment from nki functions should be done on memory regions and have a form of foo(b, dst=a[...])"
    | none => return .letM p ty e
  | .setM x e accum =>
    match <- rewriteOp e x with
    | some op =>
      warn "Mutating assignment (a[...] = foo(...)) form is deprecated. Use foo(..., dst=a[...]) instead"
      return op
    | none => return .setM x e accum
  -- reccur on statemtns
  | .ifStm e thn els => return .ifStm e (<- stmts thn) (<- stmts els)
  | .forLoop x iter body => return .forLoop x iter (<- stmts body)
  -- statments that only contain expressions don't need to be considered and can be simply passed back
  | .expr _ | .assert _ | .ret _ | .declare _ _ | .breakLoop | .continueLoop => return s
  termination_by sizeOf s
end

private def func (f : Fun) : SimplifyOp Fun :=
  return {
    name := f.name
    file := f.file
    line := f.line
    args := f.args
    body := <- stmts f.body
  }

private def kernel (k : Kernel) : SimplifyOp Kernel := do
  let funs <- k.funs.mapM func
  return {
    entry   := k.entry
    funs    := funs
    args    := k.args
    globals := k.globals
  }

def simplifyOperators (k : Kernel) : Err (Kernel × List PosError) :=
  match (kernel k).run {} with
  | .ok x s => .ok (x, s.warnings.toList ++ s.newWarns.toList)
  | .error e _ => .error (toString e)
