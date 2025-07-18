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

import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util

/-!
# Definitions for Tensor representations
-/
namespace KLR.Core
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

-- Memory types on hardware
@[serde tag = 110]
inductive Memory where
  | hbm | sbuf | pmem | reg
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
Tensor element types supported by hardware.

The HW always performs operations on 32-bit types. However, when reading from
or writing to memory, automatic conversion to and from the following types is
supported.
-/
@[serde tag = 111]
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
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
A tensor shape is a list of the sizes of each dimension of the tensor. By
convention, the first dimension is always the "partition" dimension, and the
remaining dimensions are "free" dimensions. When laid out in memory, the
partition dimension will correspond to the memory partition.
-/
@[serde tag = 112]
structure Shape where
  parDim : Nat
  freeDims : List Nat
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace Shape

def toList (shape : Shape) : List Nat :=
  shape.parDim :: shape.freeDims

def fromList : List Nat -> Err Shape
  | [] => throw "invalid shape"
  | p :: f => return ⟨ p, f ⟩

def freeElements (shape : Shape) : Nat :=
  shape.freeDims.foldl (. * .) 1

instance : Inhabited Shape where
  default := { parDim := 0, freeDims := [] }

instance : ToString Shape where
  toString shape := toString shape.toList

end Shape

/-
An Address represents a region of memory. Each address has a memory type, and
the starting location and size of the memory region. The memory regions are
always two-dimensional and the start and size are expressed in bytes. The
starting location can be omitted to have the compiler choose this for you.

The Address structure is represented as a "pointer" term during tracing.
-/
@[serde tag = 113]
structure Address where
  memory : Memory
  parSize : Nat
  freeSize : Nat
  parOffset : Option Nat := none
  freeOffset : Option Nat := none
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace Address

def defaultSize (shape : Shape) (dtype : Dtype) : (Nat × Nat) :=
  (shape.parDim, shape.freeElements * dtype.size)

def withDefaultSize (addr : Address) (shape : Shape) (dtype : Dtype) : Address :=
  let (p, f) := defaultSize shape dtype
  { addr with parSize := p, freeSize := f }

instance : Inhabited Address where
  default := {
    memory := .sbuf
    parSize := 0
    freeSize := 0
  }

end Address

/--
TensorSram represents a tensor in SRam (either SBuf of PSum) at runtime. Each
runtime tensor has a dtype, shape, and address. The address size must be large
enough to hold the tensor. Unlike a TensorView, a TensorSram may not yet have
an address assigned, or it may be spilled by the allocator and need to be
reloaded. If a TensorSram has a complete Address, it can be converted to a
TensorView, if there is enough space in the SBuf (or PSum).
-/
@[serde tag = 114]
structure TensorSram where
  name    : String
  dtype   : Dtype
  shape   : Shape
  flattenedFreeElements : Nat := shape.freeElements
  address : Address
  parWF   : shape.parDim <= address.parSize
  freeWF  : shape.freeElements * dtype.size <= address.freeSize
  deriving Repr

instance : BEq TensorSram where
  beq l r := l.name == r.name &&
             l.dtype == r.dtype &&
             l.shape == r.shape &&
             l.address == r.address
-- TODO
instance : FromCBOR TensorSram := ⟨ fun _ => throw "" ⟩
instance : FromJson TensorSram := ⟨ fun _ => throw "" ⟩
instance : FromSexp TensorSram := ⟨ fun _ => throw "" ⟩
instance : ToCBOR TensorSram := ⟨ fun _ => default ⟩
instance : ToSexp TensorSram := ⟨ fun _ => default ⟩
instance : ToJson TensorSram := ⟨ fun _ => default ⟩

namespace TensorSram

-- TODO: should .mk be private?
def make (name : String)
         (dtype : Dtype)
         (shape : Shape)
         (addr : Option Address) : Err TensorSram := do
  let addr := addr.getD (Address.withDefaultSize default shape dtype)
  if parWF : shape.parDim <= addr.parSize then
    if freeWF : shape.freeElements * dtype.size <= addr.freeSize then
      return ⟨ name, dtype, shape, shape.freeElements, addr, parWF, freeWF ⟩
  throw "Tensor does not fit within memory location"

def withShape (name : TensorSram) (shape : Shape) : Err TensorSram :=
  make name.name name.dtype shape (name.address.withDefaultSize shape name.dtype)

end TensorSram

/--
Basic indexing elements: integers and slices.
These are used for basic indexing, such as:
  t[1, 2]
  t[0:10, :]
  t[5, 0:10:2]

The tracing process will generate Indexes relative to a given shape,
and therefore we do not have `None` or `...` as possibilities.
-/
@[serde tag = 115]
structure Slice where
  l : Nat
  u : Nat
  step : Int
  wf : step ≠ 0
  --deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
  deriving BEq, Repr

-- TODO
instance : FromCBOR Slice := ⟨ fun _ => throw "" ⟩
instance : FromJson Slice := ⟨ fun _ => throw "" ⟩
instance : FromSexp Slice := ⟨ fun _ => throw "" ⟩
instance : ToCBOR Slice := ⟨ fun _ => default ⟩
instance : ToSexp Slice := ⟨ fun _ => default ⟩
instance : ToJson Slice := ⟨ fun _ => default ⟩

namespace Slice

def make (l u : Nat) (step : Int) : Err Slice := do
  if wf : step ≠ 0 then
    return Slice.mk l u step wf
  throw "Step size cannot be 0"

instance : Inhabited Slice where
  default := Slice.mk 0 1 1 Int.one_ne_zero

def make! (l u : Nat) (step : Int) : Slice := get! $  make l u step

def size (slice : Slice) : Nat :=
  let step := slice.step
    if step < 0 then (slice.l - slice.u) / step.natAbs
    else natDivCeil (slice.u - slice.l) step.toNat

#guard (make! 0 10 1).size == 10
#guard (make! 10 0 (-1)).size == 10
#guard (make! 0 10 (-1)).size == 0
#guard (make! 10 0 1).size == 0

end Slice

@[serde tag = 116]
inductive Index where
  | coord (e : Nat)
  | slice (slice : Slice)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- Compute the number of elements an index represents
def Index.size : Index -> Nat
 | .coord _ => 1
 | .slice s => s.size

/--
Complete Basic Indexing expression

The number of indexes must match the dimension of the tensor.
-/

@[serde tag = 117]
structure AccessBasic where
  tensor : TensorSram
  indexes : List Index
  lenWF : tensor.shape.freeDims.length + 1 = indexes.length
  deriving Repr

instance : BEq AccessBasic where
  beq l r := l.tensor == r.tensor && l.indexes == r.indexes

-- TODO
instance : FromCBOR AccessBasic := ⟨ fun _ => throw "" ⟩
instance : FromJson AccessBasic := ⟨ fun _ => throw "" ⟩
instance : FromSexp AccessBasic := ⟨ fun _ => throw "" ⟩
instance : ToCBOR AccessBasic := ⟨ fun _ => default ⟩
instance : ToSexp AccessBasic := ⟨ fun _ => default ⟩
instance : ToJson AccessBasic := ⟨ fun _ => default ⟩

namespace AccessBasic

def make (t : TensorSram) (i : List Index) : Err AccessBasic := do
  if lenWF : t.shape.freeDims.length + 1 = i.length then
    return ⟨ t, i, lenWF ⟩
  throw "invalid basic access"

def shape (a : AccessBasic) : Err Shape :=
  if let p::l := a.indexes then
    .ok ⟨ p.size, l.map Index.size ⟩
  else .error "invalid access"

def shape! (a : AccessBasic) : Shape := get! (shape a)

theorem shape.noFail :
  forall (a : AccessBasic), AccessBasic.shape a ≠ Except.error s := by
  intro a
  unfold AccessBasic.shape
  let { tensor, indexes, lenWF : AccessBasic } := a
  induction indexes <;> simp ; trivial
  done

end AccessBasic

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
@[serde tag = 118]
structure APPair where
  step : Int := 1
  num : Nat := 1
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

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

@[serde tag = 119]
structure AccessPattern where
  tensor : TensorSram
  parNum : Nat
  freePattern : List APPair
  offset : Nat := 0
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace AccessPattern

def shape (ap : AccessPattern) : Shape :=
  .mk ap.parNum $ ap.freePattern.map fun pair => pair.num

-- Partitions are not counted in bytes or elements; I'll call them logical "rows".
def partitionRowOffset (ap : AccessPattern) : Nat :=
  ap.tensor.address.parOffset.getD 0

def freeByteOffset (ap : AccessPattern) : Nat :=
  ap.tensor.address.freeOffset.getD 0 + ap.offset

-- We can't find documentation that the free offset must be aligned by dtype size, but we think
-- it's probably the case. It certainly makes calculating indexes easier so we're going with it
-- for now.
def freeElementOffset (ap : AccessPattern) : Nat :=
  ap.freeByteOffset / ap.tensor.dtype.size

end AccessPattern

-- Tensor access: whole tensor (simple), basic indexing, or access pattern
-- TODO: add advanced indexing (tensor indirect) inductive Access where

@[serde tag = 120]
inductive Access where
  | simple  (tensor : TensorSram) : Access
  | basic   (access : AccessBasic) : Access
  | pattern (access : AccessPattern) : Access
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace Access

def mkBasic (t : TensorSram) (i : List Index) : Err Access :=
  return .basic (<- AccessBasic.make t i)

def tensor : Access -> TensorSram
  | simple tensor
  | basic {tensor, ..}
  | pattern {tensor, ..} => tensor

def shape : Access -> Err Shape
  | .simple t => return t.shape
  | .basic b => b.shape
  | .pattern ap => return ap.shape

theorem shape.noFail :
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
def shapePure (a : Access) : Shape :=
  match m:a.shape with
  | .ok x => x
  | .error _ =>
     have h : False := by apply (shape.noFail a); trivial
     nomatch h

end Access

/-
A tensor access pattern in HBM. The address is an offset into HBM.
-/
@[serde tag = 121]
structure HbmTensor where
  name : String
  dtype   : Dtype
  address : Nat
  dims : List APPair
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- register number
abbrev Reg := Nat

@[serde tag = 122]
inductive ParQuadrant where
  | par0 | par32 | par64 | par96
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
A structure representing the layout of a tensor in SRam. This maps very closely
to the way that the ISA expects tensor accesses to be expressed. Specifically,
it separates the parallel dimension from the rest of the dimensions and
includes constraints like the fact that the parallel dimension stride is always 1.

              0┌──────────────────────┐
               │                      │
             32│                      │
               │                      │
             64│                      │
               │                      │
parQuadrant─►96│    ┌───────┐│        │
               │    └───────┘│parSize │
               └──────────────────────┘
                    ▲
                    │
               parOffset
-/
@[serde tag = 123]
structure TensorView where
  name    : String
  dtype   : Dtype
  -- Which parallel dimension channel this tensor starts at
  parQuadrant : ParQuadrant
  -- The size of this tensor in the parallel dimension
  parDim : Nat
  -- The offset in the partition channel of this tensor
  freeOffset : Nat := 0
  -- The length and stride of each dimension besides the first
  freePattern: List APPair
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
The type that is passed to instructions to refer to a tensor in SBUF. We abstract
over whether the tensor is a literal or stored in a shape register.
-/
@[serde tag = 124]
inductive TensorRef where
  | abstract (access : Access)
  | literal (view : TensorView)
  | register (reg : Reg)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
This type reprents tensor arguments that can be passed to kernel function.
Tensor arguments can be either HBM or abstract SRAM tensors.
-/
@[serde tag = 125]
inductive TensorArg where
  | hbm (tensor : HbmTensor)
  | sram (tensor : TensorSram)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
