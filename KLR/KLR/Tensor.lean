/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Init.Data.Int.Basic
import KLR.Core.Operators
import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util
import Lean

namespace KLR.KLR
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, Repr

inductive Memory where
  | hbm | sbuf | pmem | reg
  deriving Repr, BEq

/-
Tensor element types supported by HW and available from NKI.

The HW always performs operations on 32-bit types. However, when reading from
or writing to memory, automatic conversion to and from the following types is
supported.
-/
inductive Dtype where
  | bfloat16
  | float8e3 | float8e4 | float8e5
  | float16 | float32 | float32r
  | int8 | int16 | int64 | int32
  | uint8 | uint16 | uint32 | uint64
  with
    @[computed_field]
    size : Dtype -> Nat
    | .uint8 | .int8 | .float8e3 | .float8e4 | .float8e5 => 1
    | .uint16 | .int16 | .bfloat16 | .float16 => 2
    | .uint32 | .int32 | .float32 | .float32r => 4
    | .uint64 | .int64 => 8
    @[computed_field]
    isInt : Dtype -> Bool
    | .int8 | .int16 | .int64 | .int32
    | .uint8 | .uint16 | .uint32 | .uint64 => true
    | _ => false

  deriving Repr, BEq

/- ALU operations supported by the HW -/
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

namespace AluOp

def isBitwise : AluOp -> Bool
  | arith_shift_left
  | arith_shift_right
  | bitwise_not
  | bitwise_and
  | bitwise_or
  | bitwise_xor
  | logical_shift_left
  | logical_shift_right
  | bypass => true
  | _ => false

def isArith : AluOp -> Bool
  | .bypass => true
  | op => not op.isBitwise

instance : ToString AluOp where
  toString op := reprStr op

end AluOp

inductive Const where
  | int (i : Int32)
  | float (f : Float32)
  deriving BEq, Repr

namespace Const

def isInt : Const -> Bool
  | .int _ => true | _ => false

def isFloat : Const -> Bool
  | .float _ => true | _ => false

instance : ToString Const where
  toString
  | .int i => toString i
  | .float f => toString f

end Const

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
  partitionOffset : Option Nat := none
  freeOffset : Option Nat := none
  parent : Option Address := none
  deriving Repr, BEq

namespace Address

def defaultSize (shape : Shape) (dtype : Dtype) : (Nat × Nat) :=
  (shape.parDim, shape.freeElements * dtype.size)

def withDefaultSize (addr : Address) (shape : Shape) (dtype : Dtype) : Address :=
  { addr with size := defaultSize shape dtype }

end Address

/--
TensorName represents a tensor in memory at runtime. Each runtime tensor has a
dtype, shape, and address. The address size must be large enough to hold the
tensor.
-/

structure TensorName where
  name    : String
  dtype   : Dtype
  shape   : Shape
  address : Address
  parWF   : shape.parDim <= address.size.fst
  freeWF  : shape.freeElements * dtype.size <= address.size.snd
  deriving Repr

namespace TensorName

def make (name : String)
         (dtype : Dtype)
         (shape : Shape)
         (addr : Option Address) : Err TensorName := do
  let addr := addr.getD { memory := .sbuf, size := Address.defaultSize shape dtype }
  if parWF: shape.parDim <= addr.size.fst then
    if freeWF: shape.freeElements * dtype.size <= addr.size.snd then
      return ⟨ name, dtype, shape, addr, parWF, freeWF ⟩
  throw "Invalid tensor"

def withShape (name : TensorName) (shape : Shape) : Err TensorName :=
  make name.name name.dtype shape (name.address.withDefaultSize shape name.dtype)

instance : BEq TensorName where
  beq l r := l.name == r.name &&
             l.dtype == r.dtype &&
             l.shape == r.shape &&
             l.address == r.address

end TensorName

/--
Basic indexing elements: integers and slices.
These are used for basic indexing, such as:
  t[1, 2]
  t[0:10, :]
  t[5, 0:10:2]

The tracing process will generate Indexes relative to a given shape,
and therefore we do not have `None` or `...` as possibilities.
-/
structure Slice where
  l : Nat
  u : Nat
  step : Int
  wf : step ≠ 0
deriving Repr

namespace Slice

def make (l u : Nat) (step : Int) : Err Slice :=
  if H : step == 0 then throw "step can't be 0"
  else return Slice.mk l u step (by simp_all)

instance : Inhabited Slice where
  default := Slice.mk 0 1 1 (by omega)

def make! (l u : Nat) (step : Int) : Slice := get! $  make l u step

instance : BEq Slice where
  beq s1 s2 := s1.l == s2.l && s1.u == s2.u && s1.step == s2.step

def size (slice : Slice) : Nat :=
  let step := slice.step
    if step < 0 then (slice.l - slice.u) / step.natAbs
    else natDivCeil (slice.u - slice.l) step.toNat

#guard (make! 0 10 1).size == 10
#guard (make! 10 0 (-1)).size == 10
#guard (make! 0 10 (-1)).size == 0
#guard (make! 10 0 1).size == 0

end Slice

inductive Index where
  | coord (e : Nat)
  | slice (slice : Slice)
  deriving Repr, BEq

-- Compute the number of elements an index represents
def Index.size : Index -> Nat
 | .coord _ => 1
 | .slice s => s.size

/--
Complete Basic Indexing expression

The number of indexes must match the dimension of the tensor.
-/

structure AccessBasic where
  tensor : TensorName
  indexes : List Index
  lenWF : tensor.shape.freeDims.length + 1 = indexes.length
  deriving Repr

instance : BEq AccessBasic where
  beq l r := l.tensor == r.tensor && l.indexes == r.indexes

def AccessBasic.make (t : TensorName) (i : List Index) : Err AccessBasic := do
  if lenWF : t.shape.freeDims.length + 1 = i.length then
    return ⟨ t, i, lenWF ⟩
  throw "invalid basic access"

def AccessBasic.shape (a : AccessBasic) : Err Shape :=
  if let p::l := a.indexes then
    .ok ⟨ p.size, l.map Index.size ⟩
  else .error "invalid access"

theorem AccessBasic.shape.noFail :
  forall (a : AccessBasic), AccessBasic.shape a ≠ Except.error s := by
  intro a
  unfold AccessBasic.shape
  let { tensor, indexes, lenWF : AccessBasic } := a
  induction indexes <;> simp ; trivial
  done

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
offset. In NKI, the first access pattern pair corresponds to the partition
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
  tensor : TensorName
  parNum : Nat
  freePattern : List APPair
  offset : Nat := 0
  deriving Repr, BEq

namespace AccessPattern

def shape (ap : AccessPattern) : Shape :=
  .mk ap.parNum $ ap.freePattern.map fun pair => pair.num

private def withNoParents (ap : AccessPattern) (f : AccessPattern -> a) : Err a :=
  if ap.tensor.address.parent.isSome
    then throw "Please compile away the parent indirections"
  else return f ap

-- Partitions are not counted in bytes or elements; I'll call them logical "rows".
def partitionRowOffset (ap : AccessPattern) : Err Nat := ap.withNoParents fun ap =>
  ap.tensor.address.partitionOffset.getD 0

private def freeByteOffset' (ap : AccessPattern) := ap.tensor.address.freeOffset.getD 0 + ap.offset

def freeByteOffset (ap : AccessPattern) : Err Nat := ap.withNoParents freeByteOffset'

-- We can't find documentation that the free offset must be aligned by dtype size, but we think
-- it's probably the case. It certainly makes calculating indexes easier so we're going with it
-- for now.
def freeElementOffset (ap : AccessPattern) : Err Nat := ap.withNoParents fun ap =>
  ap.freeByteOffset' / ap.tensor.dtype.size

end AccessPattern

-- Tensor access: whole tensor (simple), basic indexing, or access pattern
-- TODO: add advanced indexing (tensor indirect) inductive Access where

inductive Access where
  | simple  : TensorName -> Access
  | basic   : AccessBasic -> Access
  | pattern : AccessPattern -> Access
  deriving Repr, BEq

def Access.mkBasic (t : TensorName) (i : List Index) : Err Access :=
  return .basic (<- AccessBasic.make t i)

def Access.tensor : Access -> TensorName
  | simple tensor | basic {tensor, ..} | pattern {tensor, ..} => tensor

def Access.shape : Access -> Err Shape
  | .simple t => return t.shape
  | .basic b => b.shape
  | .pattern ap => return ap.shape

theorem Access.shape.noFail :
  forall (a : Access), Access.shape a ≠ Except.error s := by
  unfold Access.shape pure
  unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold Except.instMonad Except.pure
  intro a
  induction a <;> simp
  apply AccessBasic.shape.noFail
  done

-- We could make a pure variant of shape, but proofs about this
-- function may be difficult due to the dependent matching
def Access.shapePure (a : Access) : Shape :=
  match m:a.shape with
  | .ok x => x
  | .error _ =>
     have h : False := by apply (shape.noFail a); trivial
     nomatch h
