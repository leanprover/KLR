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

/--
Basic indexing elements: integers and slices.
These are used for basic indexing, such as:
  t[1, 2]
  t[0:10, :]
  t[5, 0:10:2]
-/
inductive Index where
  | coord (e : Int)
  | slice (l u step : Option Int)
  deriving Repr, BEq

/--
Access pattern elements.

These are used for HW-native indexing which consists of an offset and a list
of access pattern pairs. Each pair specifies a step size and the number of
steps to take. The first pair corresponds to the partition dimension and
changes the slowest; the last pair changes the fastest. For example, in the
list of pairs:

  [ (3,2), (1,3) ]

the first pair will produce the values 0,3 and the second pair will produce the
values 0,1,2. Added together, the pairs produce the values:

  0, 1, 2, 3, 4, 5.

which is equivalent to the basic index [0:2,0:3] for a standard tensor layout.
-/
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

/--
Expressions are trivial right now, waiting on dynamic loops.

The call expression would only appear in a KLR program if the tracer
encountered an unknown function.
-/
inductive Expr where
  | value (v : Value)
  | call (f : String) (args : List Value) (kwargs : List (String × Value))
  deriving Repr, BEq

inductive Stmt where
  | ret (v : Value)
  | assign (x : String) (e : Expr)
  | store (dst : Access) (op : Operator) (args : List Value)
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

end Access

class Tensors (a : Type) where
  tensors : a -> List TensorName
export Tensors (tensors)

instance : Tensors TensorName where
  tensors tn := [tn]

-- TODO: not efficient
instance [inst : Tensors a] : Tensors (List a) where
  tensors l := (l.flatMap tensors).eraseDups

instance : Tensors Access where
  tensors a := [a.tensor]

instance : Tensors Value where
  tensors
  | .access a => tensors a
  | _ => []

instance : Tensors Expr where
  tensors
  | .value v => tensors v
  | .call _ args kwargs => tensors (args ++ kwargs.map Prod.snd)

instance : Tensors Stmt where
  tensors
  | .ret v => tensors v
  | .assign _ e => tensors e
  | .store dst _ vs => tensors (tensors dst :: vs.map tensors)

def Kernel.internal (k : Kernel) : List TensorName :=
  let ts := (k.body.map tensors).flatten.eraseDups
  (ts.removeAll k.inputs).removeAll k.outputs
