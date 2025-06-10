/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Basic

/-
Lowering passes: from NKI to NKI.
-/

namespace KLR.NKI

/-
# Positional argument passing

Simplify function calls by turning keyword arguments and default parameters
into positional arguments.

This will aide the type checker by making all function arguments explicit.

Note: We can only handle calls where the function is a simple variable reference.
Things like this are syntactically valid python:
```python
def f(x):
  return x

def g():
  return 42

def h(flag, x):
  return (f if flag else g)(x)
```
Calling `h` will only result in a runtime error if `flag` is `False`.
-/

/--
Unify all positional, keyword, and default arguments into one list of positional arguments

Note:
- If an argument is missing, the output will also contain missing arguments and mess up the order
of later arguments.
- Unknown keyword arguments are discarded.
-/
def unifyArgs (args : List Expr) (keywords : List Keyword) (params : List Param) : List Expr :=
  match args, params with
  | [], [] => []
  | [], paramHd :: paramTl =>
    -- Ran out of positional arguments, look for keyword args first
    match keywords.find? (·.name = paramHd.name) with
    | some { expr .. } => expr :: unifyArgs [] keywords paramTl
    | none =>
      -- No keyword arg passed in, look for a default value
      match paramHd.dflt with
      | some dflt => dflt :: unifyArgs [] keywords paramTl
      | none => unifyArgs [] keywords paramTl
  | args, [] => args
  | argHd :: argTl, _ :: paramTl => argHd :: unifyArgs argTl keywords paramTl

mutual

def Expr.positionalArgs (funs : List Fun) : Expr → Expr
  | { expr, pos } => ⟨expr.positionalArgs funs, pos⟩

def Expr'.positionalArgs (funs : List Fun) (e : Expr') : Expr' :=
  match e with
  | .value v => .value v
  | .var name => .var name
  | .proj e name => .proj (e.positionalArgs funs) name
  | .tuple elems => .tuple (elems.map <| Expr.positionalArgs funs)
  | .access e is => .access (e.positionalArgs funs) (is.map <| Index.positionalArgs funs)
  | .binOp op e1 e2 => .binOp op (e1.positionalArgs funs) (e2.positionalArgs funs)
  | .ifExp test body orelse => .ifExp (test.positionalArgs funs) (body.positionalArgs funs) (orelse.positionalArgs funs)
  | .call ⟨fexpr, fpos⟩ posArgs keywords =>
    -- Only handle simple function calls
    match fexpr with
    | .var fname =>
      match funs.find? (·.name = fname) with
      | some { args := params, .. } =>
        .call ⟨fexpr, fpos⟩ (unifyArgs posArgs keywords params) []
      | none => e
    | _ => e

def Index.positionalArgs (funs : List Fun) : Index → Index
  | .coord i => .coord (i.positionalArgs funs)
  | .slice l u step =>
    -- Using `Option.map` here makes the termination checker fail
    let l :=
      match l with
      | .some l => .some (l.positionalArgs funs)
      | .none => .none
    let u :=
      match u with
      | .some u => .some (u.positionalArgs funs)
      | .none => .none
    let step :=
      match step with
      | .some step => .some (step.positionalArgs funs)
      | .none => .none
    .slice l u step

end

mutual

def Stmt.positionalArgs (funs : List Fun) : Stmt → Stmt
  | ⟨stmt, pos⟩ => ⟨stmt.positionalArgs funs, pos⟩

def Stmt'.positionalArgs (funs : List Fun) (stmt : Stmt') : Stmt' :=
  match stmt with
  | .expr e => .expr (e.positionalArgs funs)
  | .assert e => .assert (e.positionalArgs funs)
  | .ret e => .ret (e.positionalArgs funs)
  | .assign x ty e =>
    let x := x.positionalArgs funs
    let ty := ty.map (Expr.positionalArgs funs)
    let e := e.map (Expr.positionalArgs funs)
    .assign x ty e
  | .ifStm e thn els =>
    let e := e.positionalArgs funs
    let thn := thn.map (Stmt.positionalArgs funs)
    let els := els.map (Stmt.positionalArgs funs)
    .ifStm e thn els
  | .forLoop x iter body =>
    let x := x.positionalArgs funs
    let iter := iter.positionalArgs funs
    let body := body.map (Stmt.positionalArgs funs)
    .forLoop x iter body
  | .breakLoop => .breakLoop
  | .continueLoop => .continueLoop

end

def Param.positionalArgs (funs : List Fun) : Param → Param
  | ⟨name, dflt⟩ => ⟨name, dflt.map (Expr.positionalArgs funs)⟩

def Fun.positionalArgs (funs : List Fun) : Fun → Fun
  | { name, file, line, body, args } =>
    let body := body.map (Stmt.positionalArgs funs)
    let args := args.map (Param.positionalArgs funs)
    { name, file, line, body, args }

def Arg.positionalArgs (funs : List Fun) : Arg → Arg
  | { name, value } => ⟨name, value.positionalArgs funs⟩

def Kernel.positionalArgs : Kernel → Kernel
  | { entry, funs, args, globals } =>
    let funs := funs.map (Fun.positionalArgs funs)
    let args := args.map (Arg.positionalArgs funs)
    let globals := globals.map (Arg.positionalArgs funs)
    { entry, funs, args, globals }

end KLR.NKI
