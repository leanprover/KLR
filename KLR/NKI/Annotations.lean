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
import KLR.Util

/-
Process annotations found in NKI programs.

For instance, for loops of the form:

  for i in affine_range(...): ...

are considered a special syntactic form that must be written in just this way
to effect the "affine" annotation. The use of affine_range in other contexts
will generate a warning and be treated as a call to range.
-/

namespace KLR.NKI
open Compile.Pass

abbrev Ann := Pass Unit

-- Expressions

private def checkName : Name -> Ann Name
  | .str _ "range" => return `range
  | .str _ "static_range"
  | .str _ "affine_range"
  | .str _ "sequential_range" => do
    warn "annotation has no effect"
    return `range
  | n => return n

mutual
private def expr (e : Expr) : Ann Expr :=
  withPos e.pos do return { e with expr := <- expr' e.expr }
  termination_by sizeOf e
  decreasing_by cases e; simp; omega

private def exprs (l : List Expr) : Ann (List Expr) :=
  l.mapM expr
  termination_by sizeOf l

private def expr' (e' : Expr') : Ann Expr' :=
  match e' with
  | .value v => return .value v
  | .var n => return .var (<- checkName n)
  | .tuple es => return .tuple (<- exprs es)
  | .list es => return .list (<- exprs es)
  | .dict es => return .dict (<- es.mapM keyword)
  | .access e l => return .access (<- expr e) (<- l.mapM index)
  | .binOp op l r => return .binOp op (<- expr l) (<- expr r)
  | .conj l r => return .conj (<- expr l) (<- expr r)
  | .disj l r => return .disj (<- expr l) (<- expr r)
  | .ifExp c t f => return .ifExp (<- expr c) (<- expr t) (<- expr f)
  | .call f args kws => return .call (<- expr f) (<- exprs args) (<- kws.mapM keyword)
  | .object c fs => return .object c (<- fs.mapM keyword)
  | .format e r => return .format (<- expr e) r
  | .joined es => return .joined (<- exprs es)
  termination_by sizeOf e'

private def optExpr (oe : Option Expr) : Ann (Option Expr) :=
  match oe with
  | none => return none
  | some e => return some (<- expr e)
  termination_by sizeOf oe

private def index (i : Index) : Ann Index :=
  match i with
  | .coord e => return .coord (<- expr e)
  | .slice l u s => return .slice (<- optExpr l) (<- optExpr u) (<- optExpr s)
  | .ellipsis => return .ellipsis
  termination_by sizeOf i

private def keyword (kw : Keyword) : Ann Keyword :=
  match kw with
  | ⟨ name, e ⟩ => return ⟨ name, <- expr e ⟩
  termination_by sizeOf kw
end

-- Statements

private def rangeType : Name -> Ann RangeType
  | .str _ "range" => return .static
  | .str _ "static_range" => return .static
  | .str _ "affine_range" => return .affine
  | .str _ "sequential_range" => return .sequential
  | n => throw s!"{n} is not a supported iterator"

private def iterator : Iterator -> Ann Iterator
  | .range ty l u s => return .range ty l u s
  | .expr e => withPos e.pos do
    let zero := Expr.mk (.value $ .int 0) e.pos
    let one  := Expr.mk (.value $ .int 1) e.pos
    match e.expr with
    | .call ⟨.var n, _⟩ args [] =>
      let ty <- rangeType n
      match args with
      | [u] => return .range ty zero u one
      | [l,u] => return .range ty l u one
      | [l,u,s] => return .range ty l u s
      | _ => throw "invalid range arguments"
    | _ => return .expr e

mutual
private def stmt (s : Stmt) : Ann Stmt :=
  withPos s.pos do return { s with stmt := <- stmt' s.stmt }
  termination_by sizeOf s
  decreasing_by cases s; simp; omega

private def stmts (l : List Stmt) : Ann (List Stmt) := do
  l.mapM stmt
  termination_by sizeOf l

private def stmt' (s : Stmt') : Ann Stmt' := do
  match s with
  | .expr e => return .expr (<- expr e)
  | .assert e => return .assert (<- expr e)
  | .ret e => return .ret (<- expr e)
  | .declare n e => return .declare n (<- expr e)
  | .letM p ty e => return .letM p (<- optExpr ty) (<- expr e)
  | .setM x e accum => return .setM (<- expr x) (<- expr e) accum
  | .ifStm c t e => return .ifStm c (<- stmts t) (<- stmts e)
  | .forLoop x iter body => do return .forLoop x (<- iterator iter) (<- stmts body)
  | .breakLoop => return .breakLoop
  | .continueLoop => return .continueLoop
  termination_by sizeOf s
end

private def func (f : Fun) : Ann Fun :=
  return { f with body := <- stmts f.body }

private def class_ (c : Class) : Ann Class :=
  return { c with methods := <- c.methods.mapM func }

private def arg (a : Arg) : Ann Arg := do
  return { a with value := <- expr a.value }

def annotate (k : Kernel) : Ann Kernel := do
  return {
    entry   := k.entry
    funs    := <- k.funs.mapM func
    cls     := <- k.cls.mapM class_
    args    := <- k.args.mapM arg
    globals := <- k.globals.mapM arg
    grid    := k.grid
    edges   := k.edges
  }
