/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Simplify
import KLR.NKI.Types

/-!
# Typed IR for NKI

This includes the following simplications
- Tuples are removed
- Function calls are curried and no default or keyword args are allowed
- Binnary ops become calls of constant functions
- `Stmt`s have `seq` which removed the need for `List Stmt`
- Introduce let bindings in `Stmt`
- No un-initialized variables allowed
-/

namespace KLR.NKI

namespace TIR

inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | ellipsis
  | tensor (shape : List Nat) (dtype : Core.Dtype)

inductive Const where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and

mutual

inductive Index where
  | coord (i : Expr)
  | slice (l u step : Option Expr)

structure Expr where
  expr : Expr'
  pos : Pos

inductive Expr' where
  | const (const : Const)
  | value (value : Value)
  | var (name : String)
  | access (expr : Expr) (indices : List Index)
  | ifExp (test body orelse : Expr)
  | app (f : Expr) (arg : Expr)
  | typApp (f : Expr) (arg : Expr)

end

mutual

structure Stmt where
  stmt : Stmt'
  pos : Pos

inductive Stmt' where
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e : Expr)
  | let_ (var : String) (ty : Types.Typ) (rhs : Expr)
  | assign (lhs : Expr) (rhs : Expr)
  | ifStm (e : Expr) (thn els : Stmt)
  | forLoop (x : Expr) (iter : Expr) (body : Stmt)
  | breakLoop
  | continueLoop
  | seq (s1 s2 : Stmt)

end

structure Fun where
  name : String
  file : String
  line : Nat
  body : Stmt
  typArgs : List Types.Typ
  args : List Types.Typ

structure Kernel where
  entry : String
  typArgs : List Types.Typ
  args : List Expr
  funs : List Fun
  globals : List Arg

end TIR

/-!
# Lowering pass from basic NKI to TIR
-/

def Value.lower : Value → PosM TIR.Value
  | none => return .none
  | bool value => return .bool value
  | int value => return .int value
  | float value => return .float value
  | string value => return .string value
  | ellipsis => return .ellipsis
  | tensor shape dtype =>
    match Core.Dtype.fromString dtype with
    | .some dtype => return .tensor shape dtype
    | .none => throw s!"{dtype} is not a valid dtype"

mutual

def Expr.lowerOption : Option Expr → PosM (Option TIR.Expr)
  | some e => return some (← e.lower)
  | none => none

def Index.lower : Index → PosM TIR.Index
  | .coord i => return .coord (← i.lower)
  | .slice l u step => do
    let l ← Expr.lowerOption l
    let u ← Expr.lowerOption u
    let step ← Expr.lowerOption step
    return .slice l u step

def Expr.lower : Expr → PosM TIR.Expr
  | { expr, pos } =>
    withPos pos do
      return {expr := ← expr.lower, pos := pos}

def Expr'.lower : Expr' → PosM TIR.Expr'
  | .value value => sorry
  | .var name => sorry
  | .proj expr name=> sorry
  | .tuple elements => sorry
  | .access expr indices => do
    let expr ← expr.lower
    let indices ← indices.mapM Index.lower
    return .access expr indices
  | .binOp op left right => sorry
  | .ifExp test body orelse => sorry
  | .call f args keywords => sorry

end

mutual

def Stmt.lower : Stmt → PosM TIR.Stmt
  | { stmt, pos } =>
    withPos pos do
      return {stmt := ← stmt.lower, pos := pos}

def Stmt'.lower (stmt : Stmt') : PosM TIR.Stmt' :=
  sorry

end

def Fun.lower (f : Fun) : PosM TIR.Fun :=
  sorry

def Kernel.lower (k : Kernel) : PosM TIR.Kernel :=
  sorry
