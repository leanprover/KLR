/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Serde.Attr

/-!
# Abstract syntax of NKI functions

This AST is produced from the Python AST by simplification.
The two ASTs are similar. This one is the "official" abstract
syntax of NKI.
-/

namespace KLR.NKI

@[serde tag = 1]
structure Pos where
  line : Nat
  column : Nat
  deriving Repr

-- Note: the python int and float types are compatible with Lean's types
-- The str type may require conversion (to UTF8).
@[serde tag = 2]
inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | ellipsis
  | tensor (shape : List Nat) (dtype : String)  -- TODO use Core Dtype
  deriving Repr

@[serde tag = 3]
inductive BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving Repr

mutual
@[serde tag = 4]
structure Expr where
  expr : Expr'
  pos : Pos
  deriving Repr

@[serde tag = 5]
inductive Expr' where
  | value (value : Value)
  | var (name : String)
  | proj (expr : Expr) (name : String)
  | tuple (elements : List Expr)
  | access (expr : Expr) (indices : List Index)
  | binOp (op : BinOp) (left right : Expr)
  | ifExp (test body orelse : Expr)
  | call (f: Expr) (args: List Expr) (keywords : List Keyword)
  deriving Repr

@[serde tag = 6]
inductive Index where
  | coord (i : Expr)
  | slice (l u step : Option Expr)
  deriving Repr

@[serde tag = 7]
structure Keyword where
  name : String
  expr : Expr
  deriving Repr
end

mutual
@[serde tag = 8]
structure Stmt where
  stmt : Stmt'
  pos : Pos
  deriving Repr

@[serde tag = 9]
inductive Stmt' where
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e : Expr)
  | assign (x : Expr) (ty e : Option Expr)
  | ifStm (e : Expr) (thn els: List Stmt)
  | forLoop (x : Expr) (iter: Expr) (body: List Stmt)
  | breakLoop
  | continueLoop
  deriving Repr
end

@[serde tag = 10]
structure Param where
  name : String
  dflt : Option Expr
  deriving Repr

@[serde tag = 11]
structure Fun where
  name : String
  file : String
  line : Nat
  body : List Stmt
  args : List Param
  deriving Repr

@[serde tag = 12]
structure Arg where
  name : String
  value : Expr
  deriving Repr

@[serde tag = 13]
structure Kernel where
  entry : String
  funs : List Fun
  args : List Arg
  globals : List Arg
  deriving Repr
