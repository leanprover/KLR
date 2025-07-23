/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
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

structure SimplifyOpState where
  statements : Array Stmt := #[]

abbrev SimplifyOp := Pass SimplifyOpState

private def operatorNames : List String := [
  "nc_matmul",
  "nc_transpose",
  "activation",
  "activation_reduce",
  "tensor_reduce",
  "tensor_partition_reduce",
  "tensor_tensor",
  "tensor_tensor_scan",
  "scalar_tensor_tensor",
  "tensor_scalar",
  "tensor_scalar_reduce",
  "tensor_copy",
  "tensor_copy_dynamic_src",
  "tensor_copy_dynamic_dst",
  "tensor_copy_predicated",
  "reciprocal",
  "iota",
  "dropout",
  "affine_select",
  "range_select",
  "memset",
  "bn_stats",
  "bn_aggr",
  "local_gather",
  "dma_copy",
  "max8",
  "nc_find_index8",
  "nc_match_replace8",
  "nc_stream_shuffle"
]

private def rewriteOp (rhs: Expr) (dst: Expr) : SimplifyOp (Option Stmt') := do
  match rhs.expr with
  | .call f args kws =>
    if let .var n := f.expr then
      if operatorNames.any (fun x => x == n.toString) then
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
  match (kernel k).run {} {} with
  | .ok x s => .ok (x.1, s.warnings.toList ++ s.newWarns.toList)
  | .error e _ => .error (toString e)
