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

abbrev SimplifyOp := Pass Unit

private def isISA : Expr -> Bool
  | ⟨ .var (.str `nki.isa "register_alloc"), _ ⟩ => false
  | ⟨ .var (.str `nki.isa _), _ ⟩ => true
  | _ => false

private def rewriteOp (rhs: Expr) (dst: Expr) (accum : Bool) : SimplifyOp (Option Stmt') := do
  match rhs.expr with
  | .call f args kws =>
    if isISA f then
      -- The way we resolve args would treat first positional arg as dst even if
      -- keyword arg is present
      let args := dst :: args
      let kws := if accum then ⟨ "psumAccumulateFlag", ⟨.value (.int (1 <<< 7)), rhs.pos⟩⟩ :: kws else kws
      let call : Expr' := .call f args kws
      return some (.expr ⟨call, rhs.pos⟩)
    else
      return none
  | _ => return none

private def rewriteNdarray (stmt : Stmt') : Stmt' :=
  match stmt with
  | .letM (.var x) ty ⟨.call ⟨.var fname, p0 ⟩ args kws, p1 ⟩ =>
    let suffixes := ["nki.language.ndarray", "hbm.view", "sbuf.view", "psum.view"]
    if suffixes.any (fname.toString.endsWith ·) then
      if kws.any fun x => x.name == "name" then
       stmt
      else
        let uniqueNameCall := ⟨.call
          ⟨.var `builtin.lang.unique_name, p1⟩
          [⟨.value (.string x.toString), p1⟩]
          [],
          p1⟩
        let kws := ⟨"name", uniqueNameCall⟩ :: kws
        .letM (.var x) ty ⟨.call ⟨.var fname, p0 ⟩ args kws, p1 ⟩
    else
      stmt
  | _ => stmt

mutual
private def stmt (s : Stmt) : SimplifyOp (Stmt) := do
  return ⟨ <- stmt' s.stmt, s.pos ⟩
  termination_by sizeOf s
  decreasing_by cases s; simp; omega

private def stmts (s : List Stmt) : SimplifyOp (List Stmt) := do
  return <- s.mapM stmt
  termination_by sizeOf s

private def stmt' (s : Stmt') : SimplifyOp Stmt' := do
  let mutAssignWarning := "Mutating assignment (a[...] = foo(...)) form is deprecated. Use foo(..., dst=a[...]) instead"
  match s with
  | .letM x ty e =>
    if let .binOp _ _ ⟨.call f args kws, _⟩ := e.expr then
      if isISA f then
        if let .var xExpr := x then
          match <- rewriteOp ⟨.call f args kws, e.pos⟩ ⟨.var xExpr, e.pos⟩ true with
          | some op =>
            warn mutAssignWarning
            return op
          | none => return .letM x ty e
    if let .call f _ _ := e.expr then
      if isISA f then
        if let .var xExpr := x then
          match <- rewriteOp e ⟨.var xExpr, e.pos⟩ false with
          | some op =>
            warn mutAssignWarning
            return op
          | none => return .letM x ty e
    return rewriteNdarray s
  | .setM x e accum =>
    match <- rewriteOp e x accum with
    | some op =>
      warn mutAssignWarning
      return op
    | none => return .setM x e accum
  -- reccur on statemtns
  | .ifStm e thn els => return .ifStm e (<- stmts thn) (<- stmts els)
  | .forLoop x iter body => return .forLoop x iter (<- stmts body)
  | .whileLoop test body => return .whileLoop test (<- stmts body)
  -- statments that only contain expressions don't need to be considered and can be simply passed back
  | .expr _ | .assert _ _ | .ret _ | .declare _ _ | .breakLoop | .continueLoop => return s
  termination_by sizeOf s
end

private def func (f : Fun) : SimplifyOp Fun :=
  return { f with body := <- stmts f.body }

def simplifyOperators (k : Kernel) : SimplifyOp Kernel := do
  return { k with funs := <- k.funs.mapM func }
