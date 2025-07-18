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
Simplification pass: convert from Python Core to NKI.
-/

namespace KLR.NKI
open Compile.Pass

structure SimplifyState where
  statements : Array Stmt := #[]

abbrev Simplify := Pass SimplifyState

private def addStmt (s : Stmt) : Simplify Unit :=
  modify fun st => { st with statements := st.statements.push s }

private def getAndClearStmts : Simplify (List Stmt) := do
  modifyGet fun st => (st.statements.toList, {st with statements := #[]})

/-
# Value Simplification
-/

private def value : Python.Const -> Simplify Value
  | .none => return .none
  | .bool b => return .bool b
  | .int i => return .int i
  | .float f => return .float f
  | .string s => return .string s
  | .ellipsis => throw "invalid use of ellipsis"
  | .tensor s dty => return .tensor s dty

/-
# Operator Simplification

We combine all of the different types into a single BinOp category.
The distinction will be handled by the type system.
-/

private def boolOp : Python.BoolOp -> BinOp
  | .land => .land
  | .lor => .lor

private def cmpOp : Python.CmpOp -> Simplify BinOp
  | .eq => return .eq
  | .ne => return .ne
  | .lt => return .lt
  | .le => return .le
  | .gt => return .gt
  | .ge => return .ge
  | .is => do
    warn "the 'is' operator is not supported in NKI, use =="
    return .eq
  | .isNot => do
    warn "the 'is not' operator is not supported in NKI, use !="
    return .ne
  | .isIn | .notIn =>
    throw "the 'in' operator is not supported in NKI"

-- Use of unary operators should be rare; we convert them into function calls.
-- TODO: what names should we use for these functions?
private def unaryOp (op : Python.UnaryOp) : Simplify (Expr -> Expr') :=
  let call s e := .call ⟨.var s, e.pos⟩ [e] []
  match op with
  | .invert => return call `builtin.op.invert
  | .not => return call `builtin.op.not
  | .uadd => return fun e => e.expr
  | .usub => return call `builtin.op.negate

private def binOp : Python.BinOp -> Simplify BinOp
  | .add => return .add
  | .sub => return .sub
  | .mul => return .mul
  | .matmul => throw "the matmul operator is not supported in NKI"
  | .div => return .div
  | .mod => return .mod
  | .pow => return .pow
  | .lshift => return .lshift
  | .rshift => return .rshift
  | .or => return .or
  | .xor => return .xor
  | .and => return .and
  | .floor => return .floor

private def booleanOp (op : BinOp) : List Expr -> Simplify Expr
  | [e] => return e
  | e :: es => return ⟨ .binOp op e (<- booleanOp op es), e.pos ⟩
  | _ => throw "invalid boolean expression"

private def compare : Expr -> List BinOp -> List Expr -> Simplify Expr
  | l, [op], [y] => return ⟨ .binOp op l y, l.pos ⟩
  | l, op :: ops, e :: es => return ⟨ .binOp op l (<- compare e ops es), l.pos ⟩
  | _, _, _ => throw "invalid comparison expression"

/-
# Expression simplification

Note on termination.

The fact that Expr is a structure seems to confuse the default termination
tactics. However, the goals are easily proved by expanding the definition of
the structure with `cases`. The use of `omega` may be overkill, but the proof
is short.
-/
mutual
private def expr (e : Python.Expr) : Simplify Expr := do
  let pos := e.pos
  let e' <- withPos pos (expr' e.expr)
  return ⟨ e', pos ⟩
  termination_by sizeOf e
  decreasing_by cases e; simp; omega

private def exprs (es : List Python.Expr) : Simplify (List Expr) :=
  es.attach.mapM fun ⟨ e, _ ⟩ => expr e
  termination_by sizeOf es

private def expr' (e' : Python.Expr') : Simplify Expr' :=
  match e' with
  | .const c => return .value (<- value c)
  | .name s _ => return .var s.toName
  | .attr e id _ => do
      match <- expr e with
      | ⟨ .var s, _ ⟩ => return .var (.str s id)
      | e =>
        let n <- freshName `x
        let s := Stmt'.letM (.var n) none e
        addStmt { stmt := s, pos := e.pos }
        return .var (n.str id)
  | .tuple l _
  | .list l _ => return .tuple (<- exprs l)
  | .subscript e ndx _ => return .access (<- expr e) (<- indexes ndx)
  | .slice .. => throw "invalid use of slice"
  | .boolOp op l => return (<- booleanOp (boolOp op) (<- exprs l)).expr
  | .binOp op l r => return .binOp (<- binOp op) (<- expr l) (<- expr r)
  | .unaryOp op e => return (<- unaryOp op) (<- expr e)
  | .compare a ops l => do
      let a <- expr a
      let ops <- ops.mapM cmpOp
      let l <- exprs l
      return (<- compare a ops l).expr
  | .ifExp c t e => return .ifExp (<- expr c) (<- expr t) (<- expr e)
  | .call f args kws => do
      let f <- expr f
      let args <- exprs args
      let kws <- keywords kws
      return .call f args kws
  termination_by sizeOf e'

private def index (e : Python.Expr) : Simplify Index := do
  match e with
  | ⟨ .const .ellipsis, _ ⟩ => return .ellipsis
  | ⟨ e', p ⟩ => withPos p do return .coord ⟨ <- expr' e', p ⟩
  termination_by sizeOf e

private def indexes (e : Python.Expr) : Simplify (List Index) := do
  match e with
  | ⟨ e', p ⟩ => withPos p do
    match e' with
    | .const .ellipsis => return [.ellipsis]
    | .slice l u step => do
      let l <- l.attach.mapM fun ⟨ e, _ ⟩ => expr e
      let u <- u.attach.mapM fun ⟨ e, _ ⟩ => expr e
      let step <- step.attach.mapM fun ⟨ e, _ ⟩ => expr e
      return [.slice l u step]
    | .tuple l _ | .list l _ => l.mapM index
    | e' => return [.coord ⟨ <- expr' e', p⟩]
  termination_by sizeOf e

private def keywords (ks : List Python.Keyword) : Simplify (List Keyword) := do
  match ks with
  | [] => return []
  | ⟨ n, e, p ⟩ :: ks => withPos p do return ⟨ n, <- expr e ⟩ :: (<- keywords ks)
  termination_by sizeOf ks
end

/-
# Statement Simplification
-/

def isSimpleName : Name -> Bool
  | .str .anonymous _ => true
  | .num n _ => isSimpleName n
  | _ => false

def isLetPattern (e : Expr) : Bool :=
  match e.expr with
  | .var n => isSimpleName n
  | .tuple _ => true
  | _ => false

def pattern (e : Expr) : Simplify Pattern :=
  withPos e.pos do match e with
  | ⟨ .var n, _ ⟩ =>
    if isSimpleName n
    then return .var n
    else throw "expecting simple variable"
  | ⟨ .tuple xs, _ ⟩ =>
    let xs <- xs.mapM pattern
    return .tuple xs
  | _ => throw "expecting pattern"

def letSet (es : List Expr) : Simplify (List Pattern × Option Expr) := do
  let (lets, sets) := es.partition isLetPattern
  match lets, sets with
  | [], [] => throw "invalid assignment"
  | xs, [] => return (<- xs.mapM pattern, none)
  | xs, [x] => return (<- xs.mapM pattern, some x)
  | _, _ => throw "mutating assignments must be in separate statements"

def assign (xs : List Expr) (e : Expr) (t : Option Expr) : Simplify (List Stmt') := do
  match <- letSet xs with
  | (xs, some s) =>
    return .setM s e (accum := false) ::
            xs.map fun x => .letM x t e
  | ([], none) => throw "invalid assignment statement"
  | ([x], none) => return [.letM x t e]
  | (xs, none) =>
    let (n, xs) <- Pattern.findVar xs
    let first := .letM (.var n) t e
    let e' : Expr := ⟨ .var n, e.pos ⟩
    let rest := xs.map fun x' => .letM x' t e'
    return first :: rest

mutual
private def stmt (s : Python.Stmt) : Simplify (List Stmt) := do
  let p := s.pos
  let l <- withPos p (stmt' s.stmt)
  let extra <- getAndClearStmts
  return extra ++ l.map fun s => ⟨ s, p ⟩
  termination_by sizeOf s
  decreasing_by cases s; simp; omega

private def stmts (s : List Python.Stmt) : Simplify (List Stmt) := do
  let l <- s.attach.mapM fun ⟨ s, _ ⟩ => stmt s
  return l.flatten
  termination_by sizeOf s

private def stmt' (s : Python.Stmt') : Simplify (List Stmt') := do
  match s with
  | .pass => return []
  | .expr e => return [.expr (<- expr e)]
  | .assert e => return [.assert (<- expr e)]
  | .ret e => return [.ret (<- expr e)]
  | .assign xs e => do assign (<- exprs xs) (<- expr e) none
  | .augAssign x op e => do
      let x <- expr x
      let e <- expr e
      let rhs := Expr'.binOp (<- binOp op) x e
      assign [x] ⟨ rhs, x.pos ⟩ none
  | .annAssign x t e => do
      let x <- expr x
      let t <- expr t
      match e with
      | some e => assign [x] (<- expr e) t
      | none =>
        if let ⟨ .var n, _ ⟩ := x then
          return [.declare n t]
        else throw "invalid declaration"
  | .ifStm c t e => return [.ifStm (<- expr c) (<- stmts t) (<- stmts e)]
  | .forLoop x iter body orelse => do
      if orelse.length > 0 then
        throw "for else is not supported in NKI"
      return [.forLoop (<- expr x) (<- expr iter) (<- stmts body)]
  | .breakLoop => return [.breakLoop]
  | .continueLoop => return [.continueLoop]
  termination_by sizeOf s
end

/-
# Function simplification

In NKI, we do not support variable- or keyword-only arguments. A variable
argument parameter is an error here as it could change how the argument list is
interpreted at the call site. We do not raise an error here if there is a
variable keyword argument parameter. We can detect if there are too many
arguments at the call site and raise the error there (or ignore the extra
arguments). So, technically we allow a variable keyword argument parameter, as
long as it is always empty.
-/

private def params (args : Python.Args) : Simplify (List Param) := do
  if args.vararg.isSome then
    throw "varargs are not supported in NKI"
  if args.kwarg.isSome then
    warn "variable keyword arguments are not supported in NKI"
  if args.posonlyargs.length > 0 then
    warn "position-only arguments are not supported in NKI"
  if args.kwonlyargs.length > 0 then
    warn "keyword-only arguments are not supported in NKI"
  let defaults := args.all_defaults
  let mut params := []
  for name in args.names do
    if let some kw := defaults.find? fun k => k.id == name then
      params := Param.mk name (some (<- expr kw.value)) :: params
    else
      params := Param.mk name none :: params
  return params.reverse

private def func (f : Python.Fun) : Simplify Fun :=
  return {
    name := f.name
    file := "unknown"  -- TODO: fix me
    line := f.line
    args := <- params f.args
    body := <- stmts f.body
  }

/-
# Kernel Simplification

TODO: handle undefined symbols
-/

private def kwargs (kws : List Python.Keyword) : Simplify (List Arg) := do
  kws.mapM fun kw => return Arg.mk kw.id (<- expr kw.value)

private def args (params : List Param)
                 (args : List Python.Expr)
                 (kws : List Python.Keyword)
                 : Simplify (List Arg) := do
  let p1 := params.zip args
  let p2 := params.drop p1.length
  let mut result := p1.reverse
  for p in p2 do
    match kws.find? fun kw => kw.id == p.name with
    | none => throw s!"argument {p.name} not supplied"
    | some kw => result := (p, kw.value) :: result
  -- map and reverse list
  result.foldlM (init := []) fun l (p,e) =>
    return Arg.mk p.name (<- expr e) :: l

private def kernel (py : Python.Kernel) : Simplify Kernel := do
  let funs <- py.funcs.mapM func
  let main_fun <-
    match funs.find? fun f => f.name == py.entry with
    | none => throw s!"entry function {py.entry} not found"
    | some f => pure f
  return {
    entry   := py.entry
    funs    := funs
    args    := <- args main_fun.args py.args py.kwargs
    globals := <- kwargs py.globals
  }

-- TODO: capture warnings, make sure to call finalize
def simplify (py : Python.Kernel) : Err Kernel :=
  match (kernel py).run {} {} with
  | .ok (x, _) _ => .ok x
  | .error e _ => .error (toString e)
