/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core.Operators

/-!
# Abstract syntax of Core NKL language

This language is the result of "tracing", and is used as the
portable format, a.k.a. Kernel Language Representation (KLR).
-/
namespace KLR.Core

/-
A TensorName is essentially a typed variable, where the type must be a tensor
type. This only refers to dynamic (run-time) tensors, not trace-time tensors.
-/

abbrev Shape := List Nat

structure TensorName where
  name  : String
  dtype : Dtype
  shape : Shape
  memory: Memory
  deriving Repr, BEq

-- Basic indexing elements: integers and slices
inductive Index where
  | coord (e : Int)
  | slice (l u step : Option Int)
  deriving Repr, BEq

-- Access pattern elements
structure APPair where
  step : Int := 1
  num : Nat := 1
  deriving Repr, BEq

-- Tensor access: whole tensor (simple), basic indexing, or access pattern
-- TODO: add advanced indexing (tensor indirect)
inductive Access where
  | simple (t : TensorName)
  | basic (t : TensorName) (indexes : List Index)
  | pattern (t : TensorName) (offset : Nat) (aps : List APPair)
  deriving Repr, BEq

inductive Value where
  | var (x : String)
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | access (a : Access)
  deriving Repr, BEq

-- TODO: Expressions are trivial right now, waiting on dynamic loops
inductive Expr where
  | value (v : Value)
  | call (op : Operator) (args : List Value)
  deriving Repr, BEq

inductive Stmt where
  | ret (v : Value)
  | assign (x : String) (e : Expr)
  | store (dst : Access) (e : Expr)
  deriving Repr, BEq

structure Kernel where
  name : String
  inputs : List TensorName
  outputs : List TensorName
  body : List Stmt
  deriving Repr, BEq

-- Utilities

namespace Access

def tensor : Access -> TensorName
  | simple t | basic t .. | pattern t .. => t

def shape : Access -> Shape
  | simple t => t.shape
  | basic _ _ => panic! "TODO"
  | pattern _ _ aps => aps.map fun ap => ap.num

def tensors (a : Access) : List TensorName := [a.tensor]

end Access

def Value.tensors : Value -> List TensorName
  | .access a => a.tensors
  | _ => []

-- TODO: not efficient
private def unique : List (List TensorName) -> List TensorName
  | lls => lls.flatten.eraseDups

def Expr.tensors : Expr -> List TensorName
  | .value v => v.tensors
  | .call _ args => unique (args.map Value.tensors)

def Stmt.tensors : Stmt -> List TensorName
  | .ret v => v.tensors
  | .assign _ e => e.tensors
  | .store dst e => unique (dst.tensors :: e.tensors :: [])

def Kernel.internal (k : Kernel) : List TensorName :=
  let ts := (k.body.map Stmt.tensors).flatten.eraseDups
  (ts.removeAll k.inputs).removeAll k.outputs
