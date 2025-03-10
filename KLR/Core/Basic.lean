/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core.Operators
import KLR.Util

/-!
# Abstract syntax of Core NKL language

This language is the result of "tracing", and is used as the
portable format, a.k.a. Kernel Language Representation (KLR).
-/
namespace KLR.Core

/-
A tensor shape is a list of the sizes of each dimension of the tensor. By
convention, the first dimension is always the "partition" dimension, and the
remaining dimensions are "free" dimensions. When laid out in memory, the
partition dimension will correspond to the memory partition.
-/

structure Shape where
  parDim : Nat
  freeDims : List Nat
  deriving Repr, BEq, Inhabited

def Shape.toList (shape : Shape) : List Nat :=
  shape.parDim :: shape.freeDims

def Shape.fromList : List Nat -> Err Shape
  | [] => throw "invalid shape"
  | p :: f => return ⟨ p, f ⟩

instance : ToString Shape where
  toString shape := toString shape.toList

def Shape.freeElements (shape : Shape) : Nat :=
  shape.freeDims.foldl (. * .) 1

/-
An Address represents a region of memory. Each address has a memory type, and
the starting location and size of the memory region. The memory regions are
always two-dimensional and the start and size are expressed in bytes. The
starting location can be omitted to have the compiler choose this for you.

An address may have a parent, in which case the start is relative to the
parent's start location. This allows the user to declare a memory region with
no start address, but containing subregions with specific relative positions.

The Address structure is represented as a "pointer" term during tracing.
-/

structure Address where
  memory : Memory
  size : Nat × Nat
  start : Option Nat × Option Nat := (none, none)
  parent : Option Address := none
  deriving Repr, BEq

def Address.defaultSize (shape : Shape) (dtype : Dtype) : (Nat × Nat) :=
  (shape.parDim * dtype.size, shape.freeElements * dtype.size)

/-
TensorName represents a tensor in memory at runtime. Each runtime tensor has a
dtype, shape, and address. The address size must be large enough to hold the
tensor.
-/

structure TensorName where
  name    : String
  dtype   : Dtype
  shape   : Shape
  address : Address := {
    memory := .sbuf
    size   := Address.defaultSize shape dtype
  }
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

-- Compute the number of elements an index represents
-- Note: this assumes Index is well-formed w.r.t dim
-- TODO: pass in proof that this is well-formed
def Index.size (dim : Nat) : Index -> Nat
 | .coord _ => 1
 | .slice l u s =>
     let abs (i : Int) : Nat := if i < 0 then (-i).toNat else i.toNat
     let l := l.getD 0
     let u := u.getD dim
     let s := s.getD 1
     let l := if l < 0 then dim + l else l
     let u := if u < 0 then dim + u else u
     let s := if s < 0 then -s else s
     (abs (u - l) / s).toNat

/--
Access pattern elements.

These are used for HW-native indexing which consists of an offset and a list of
access pattern pairs. Each pair specifies a step size and the number of steps
to take. The first changes the slowest, and the last pair changes the fastest.
For example, in the list of pairs:

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

/--
Complete access patterns

A complete access pattern has a list of APPairs, a number of partitions, and an
offset. In NKI, the fist access pattern pair corresponds to the partition
dimension, and the step size of this first pair must be one. So, in the
complete access pattern, we only store the `num` field of the first pair. The
offset field allows for an arbitrary offset to be applied to each partition.

Put together, a complete access pattern would be written as:

  t[[ offset, (1, parNum), (step1,num1), (step2,num2), ... ]]

With a meaning of:

  forall p < parNum, x < num1, y < num2, ...
    offset + p + x * step1 + y * step2 + ...

The elements generated above are multiplied by the dtype size of the tensor to
get the final memory addresses.
-/

structure AccessPattern where
  parNum : Nat
  freePattern : List APPair
  offset : Nat := 0
  deriving Repr, BEq

def AccessPattern.shape (ap : AccessPattern) : Shape :=
  .mk ap.parNum $ ap.freePattern.map fun pair => pair.num

-- Tensor access: whole tensor (simple), basic indexing, or access pattern
-- TODO: add advanced indexing (tensor indirect)
inductive Access where
  | simple (t : TensorName)
  | basic (t : TensorName) (indexes : List Index)
  | pattern (t : TensorName) (ap : AccessPattern)
  deriving Repr, BEq

def Access.tensor : Access -> TensorName
  | simple t | basic t .. | pattern t .. => t

-- Note: this assumes Access is well-formed
-- TODO: require proof of well-formedness and eliminate panic
def Access.shape : Access -> Shape
  | .simple t => t.shape
  | .pattern _ ap => ap.shape
  | .basic t [] => t.shape   -- Shouldn't happen, but OK
  | .basic t (p::l) =>
      if t.shape.freeDims.length != l.length
      then panic "invalid access pattern" else
      Shape.mk (p.size t.shape.parDim)
               ((t.shape.freeDims.zip l).map fun (d,i) => i.size d)

-- Fully reduced values
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
