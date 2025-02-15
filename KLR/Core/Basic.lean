/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

/-!
# Abstract syntax of Core NKL language

This language is the result of "tracing", and is used as the
portable format, a.k.a. Kernel Language Representation (KLR).
-/
namespace KLR.Core

-- Compute Engines

inductive Engine where
  | unassigned
  | pool
  | act
  | pe
  | dma
  | dve
  | sp
  deriving BEq, Repr

-- ALU operations
-- TODO organize these into groups
inductive AluOp where
  | abs
  | add
  | arith_shift_left
  | arith_shift_right
  | average
  | bitwise_and
  | bitwise_not
  | bitwise_or
  | bitwise_xor
  | bypass
  | divide
  | elemwise_mul
  | is_equal
  | is_ge
  | is_gt
  | is_le
  | is_lt
  | logical_and
  | logical_or
  | logical_shift_left
  | logical_shift_right
  | logical_xor
  | max
  | min
  | mod
  | mult
  | not_equal
  | pow
  | rsqrt
  | subtract
  deriving BEq, Repr

/-
A TensorName is essentially a typed variable, where the type must be a tensor
type. This only refers to dynamic (run-time) tensors, not trace-time tensors.
-/

abbrev Dtype := String
abbrev Shape := List Nat

inductive Memory where
  | dram | sbuf | pmem | reg
  deriving Repr, BEq

structure TensorName where
  name  : String
  dtype : Dtype
  shape : Shape
  memory: Memory
  deriving Repr, BEq

inductive Const where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  deriving Repr, BEq

-- This corresponds to the "Quasi-Affine Expressions" in Neuron.
-- Note, `floor` is the usual integer division.
inductive IndexExpr where
  | var (name : String)
  | int (i : Int)
  | neg (expr : IndexExpr)
  | add (left right : IndexExpr)
  | mul (scalar : Int) (expr : IndexExpr)
  | floor (expr : IndexExpr) (scalar : Int)
  | ceil (expr : IndexExpr) (scalar : Int)
  | mod (expr : IndexExpr) (scalar : Int)
  deriving Repr, BEq

-- Note: `np.newindex` is represented as `(.coord none)`
inductive Index where
  | ellipsis
  | coord (e : Option IndexExpr)
  | slice (l u step : Option IndexExpr)
  deriving Repr, BEq

structure TensorScalar where
  op0 : AluOp
  const0 : Float
  reverse0 : Bool
  op1 : AluOp
  const1 : Float
  reverse1 : Bool
  deriving Repr, BEq

inductive Operator where
  | tensorScalar : TensorScalar -> Operator
  deriving Repr, BEq

inductive Expr where
  | var (x : String)
  | const (c : Const)
  | tensor (t : TensorName)
  | access (t : Expr) (ix : List Index)
  | operator (op : Operator)
  | call (f : Expr) (args : List Expr) (kwargs : List (String × Expr))
  deriving Repr, BEq

inductive Stmt where
  | ret (v : Expr)
  | store (t : TensorName) (ix : List Index) (e : Expr)
  | assign (x : String) (e : Expr)
  | loop (x : String) (l u step : IndexExpr) (body : List Stmt)
  deriving Repr, BEq

structure Kernel where
  name : String
  inputs : List TensorName
  outputs : List TensorName
  body : List Stmt
  deriving Repr, BEq

-- TODO: not efficient
partial def Expr.tensors : Expr -> List TensorName :=
  tensors []
where
  tensors (l : List TensorName) : Expr -> List TensorName
  | .var _ => l
  | .const _ => l
  | .tensor t => l.insert t
  | .access t _ => tensors l t
  | .operator _ => l
  | .call f args kwargs =>
      let l := tensors l f
      let l := args.foldl tensors l
      kwargs.foldl (fun l kw => tensors l kw.snd) l

partial def Stmt.tensors : Stmt -> List TensorName
  | .ret e => e.tensors
  | .store t _ e => e.tensors.insert t
  | .assign _ e => e.tensors
  | .loop _ _ _ _ body => (body.map tensors).flatten.eraseDups

def Kernel.internal (k : Kernel) : List TensorName :=
  let ts := (k.body.map Stmt.tensors).flatten.eraseDups
  (ts.removeAll k.inputs).removeAll k.outputs
