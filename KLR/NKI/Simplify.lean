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
Simplification pass: convert from Python Core to NKI.
-/

namespace KLR.NKI
open Compile.Pass

-- No extra state needed: use PosM instead of PassM
abbrev Simplify := PosM

/-
# Value Simplification

Note: Tensor values are handled as part of the expressions.
We can change this: it is controlled by gather.
-/

private def value : Python.Const -> Value
  | .none => .none
  | .bool b => .bool b
  | .int i => .int i
  | .float f => .float f
  | .string s => .string s
  | .ellipsis => .ellipsis

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
  | .is | .isNot => throw "the is operator is not supported in NKI, use =="
  | .isIn | .notIn => throw "the in operator is not supported in NKI"

-- Use of unary operators should be rare; we convert them into function calls.
-- TODO: what names should we use for these functions?
private def unaryOp (op : Python.UnaryOp) : Simplify (Expr -> Expr') :=
  let call s e := .call ⟨.var s, e.pos⟩ [e] []
  match op with
  | .invert => return call "invert"
  | .not => return call "not"
  | .uadd => return fun e => e.expr
  | .usub => return call "negate"

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


-- nat and shape are only used for tensor values
-- TODO: fix this in gather.
private def nat : Python.Expr' -> Simplify Nat
  | .const (.int (.ofNat n)) => return n
  | _ => throw "expecting positive interger"

private def shape : List Python.Expr -> Simplify (List Nat)
  | [] => return []
  | ⟨ e, p ⟩ :: xs => return (<- withPos p (nat e)) :: (<- shape xs)

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
  | .const c => return .value (value c)
  | .tensor s dtype => return .value (.tensor (<- shape s) dtype)
  | .name s _ => return .var s
  | .attr e id _ => do
      match <- expr e with
      | ⟨ .var s, _ ⟩ => return .var (s ++ "." ++ id)
      | e => return .proj e id
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

private def indexes (e : Python.Expr) : Simplify (List Index) := do
  match e with
  | ⟨ e', p ⟩ => withPos p do
    match e' with
    | .slice l u step => do
      let l <- l.attach.mapM fun ⟨ e, _ ⟩ => expr e
      let u <- u.attach.mapM fun ⟨ e, _ ⟩ => expr e
      let step <- step.attach.mapM fun ⟨ e, _ ⟩ => expr e
      return [.slice l u step]
    | .tuple l _ | .list l _ => return (<- exprs l).map .coord
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
def var (x : Python.Expr) : Simplify Expr := do
  match <- expr x with
  | ⟨ .var s, p ⟩ => return ⟨ .var s, p ⟩
  | _ => throw "cannot assign to expression"

def vars : List Python.Expr -> Simplify (List Expr)
  | [] => return []
  | x :: xs =>  return (<- var x) :: (<- vars xs)

def assign (xs : List Expr) (e : Expr) : Simplify (List Stmt') := do
  let asn x e : Stmt' := .assign x none (some e)
  match xs with
  | [] => throw "invalid assignment"
  | [x] => return [ asn x e ]
  | x :: xs =>
      let first := asn x e
      let rest := xs.map fun y => asn y x
      return first :: rest

mutual
private def stmt (s : Python.Stmt) : Simplify (List Stmt) := do
  let p := s.pos
  let l <- withPos p (stmt' s.stmt)
  return l.map fun s => ⟨ s, p ⟩
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
  | .assign xs e => do assign (<- vars xs) (<- expr e)
  | .augAssign x op e => do
      let x <- var x
      let e <- expr e
      let rhs := Expr'.binOp (<- binOp op) x e
      assign [x] ⟨ rhs, x.pos ⟩
  | .annAssign x t e => do
      let x <- var x
      let t <- expr t
      match e with
      | none => return [.assign x (some t) none]
      | some e => assign [x] (<- expr e)
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
    funs    := <- py.funcs.mapM func
    args    := <- args main_fun.args py.args py.kwargs
    globals := <- kwargs py.globals
  }

-- TODO: capture warnings, make sure to call finalize
def simplify (py : Python.Kernel) : Err Kernel :=
  match (kernel py).run {} with
  | .ok x _ => .ok x
  | .error e _ => .error (toString e)
