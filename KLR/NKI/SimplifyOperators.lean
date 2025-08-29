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

private def isISA : Expr -> Bool
  | ⟨ .var (.str `neuronxcc.nki.isa _), _ ⟩ => true
  | _ => false

private def rewriteOp (rhs: Expr) (dst: Expr) : SimplifyOp (Option Stmt') := do
  match rhs.expr with
  | .call f args kws =>
    if isISA f then
      if kws.any fun x => x.name == "dst" then
          throw  "Operation with destination specified should not use assignment form"
      let kws : List Keyword := ⟨ "dst",  dst⟩ :: kws
      let call : Expr' := .call f args kws
      return some (.expr ⟨call, rhs.pos⟩)
    else
      return none
  | _ => return none

private def rewriteNdarray (stmt : Stmt') : Stmt' :=
  -- hacky for now. Fixme to actually lookup names from environment
  -- this most likely belongs somewhere else
  match stmt with
  | .letM (.var x) ty ⟨.call ⟨.var fname, p0 ⟩ args kws, p1 ⟩ =>
    if fname.toString.endsWith "ndarray" || fname.toString.endsWith "view" then
      if kws.any fun x => x.name == "name" then
       stmt
      else
        let kws := ⟨"name", ⟨ .value $ .string x.toString, p1⟩⟩ :: kws
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
  match s with
  | .letM _ _ e =>
    if let .call f .. := e.expr then
      if isISA f then
        warn "ISA function does not return a value"
    return rewriteNdarray s
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
  return { f with body := <- stmts f.body }

private def kernel (k : Kernel) : SimplifyOp Kernel := do
  return { k with funs := <- k.funs.mapM func }

def simplifyOperators (k : Kernel) : Err (Kernel × List PosError) :=
  match (kernel k).run {} with
  | .ok x s => .ok (x, s.warnings.toList ++ s.newWarns.toList)
  | .error e _ => .error (toString e)
