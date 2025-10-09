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
  | hbm | sbuf | psum | reg
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- register number
abbrev Reg := Nat

@[serde tag = 131]
inductive Immediate where
  | register (reg : Reg)
  | pointer -- TODO
  | int (i : Int32)
  | float (f : Float32)
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
  | float8_e4m3fn | float8_e5m2_x4
  | float8_e4m3fn_x4 | float4_e2m1fn_x4
  with
    @[computed_field]
    size : Dtype -> Nat
    | .uint8 | .int8 | .float8e3 | .float8e4 | .float8e5 => 1
    | .uint16 | .int16 | .bfloat16 | .float16 => 2
    | .uint32 | .int32 | .float32 | .float32r => 4
    | .uint64 | .int64 => 8
    | .float8_e4m3fn => 1
    | .float8_e5m2_x4 => 4
    | .float8_e4m3fn_x4 => 4
    | .float4_e2m1fn_x4 =>  2
    @[computed_field]
    isInt : Dtype -> Bool
    | .int8 | .int16 | .int64 | .int32
    | .uint8 | .uint16 | .uint32 | .uint64 => true
    | _ => false
    @[computed_field]
    toTensorLibDtype : Dtype -> TensorLib.Dtype
    | .uint8 => TensorLib.Dtype.uint8
    | .uint16 => TensorLib.Dtype.uint16
    | .uint32 => TensorLib.Dtype.uint32
    | .uint64 => TensorLib.Dtype.uint64
    | .int8 => TensorLib.Dtype.int8
    | .int16 => TensorLib.Dtype.int16
    | .int32 => TensorLib.Dtype.int32
    | .int64 => TensorLib.Dtype.int64
    | .float16 => TensorLib.Dtype.float32
    | .float32 => TensorLib.Dtype.float32
    | .float32r => TensorLib.Dtype.float32
    | .bfloat16 => TensorLib.Dtype.float32
    | _ => TensorLib.Dtype.float32
  deriving BEq, Inhabited, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : ToString Dtype where
  toString
    | .bfloat16 => "bfloat16"
    | .float8e3 => "float8e3"
    | .float8e4 => "float8e4"
    | .float8e5 => "float8e5"
    | .float16 => "f16"
    | .float32 => "f32"
    | .float32r => "float32r"
    | .int8 => "i8"
    | .int16 => "i16"
    | .int32 => "i32"
    | .int64 => "i64"
    | .uint8 => "u8"
    | .uint16 => "u16"
    | .uint32 => "u32"
    | .uint64 => "u64"
    | .float8_e4m3fn => "float8_e4m3fn"
    | .float8_e5m2_x4 => "float8_e5m2_x4"
    | .float8_e4m3fn_x4 => "float8_e4m3fn_x4"
    | .float4_e2m1fn_x4 => "float4_e2m1fn_x4"

namespace Dtype

def fromTensorLibDtype : TensorLib.Dtype -> Dtype
  | TensorLib.Dtype.uint8 => .uint8
  | TensorLib.Dtype.uint16 => .uint16
  | TensorLib.Dtype.uint32 => .uint32
  | TensorLib.Dtype.uint64 => .uint64
  | TensorLib.Dtype.int8 => .int8
  | TensorLib.Dtype.int16 => .int16
  | TensorLib.Dtype.int32 => .int32
  | TensorLib.Dtype.int64 => .int64
  | TensorLib.Dtype.float32 => .float32
  | _ => .float32

end Dtype

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
  name : String
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
    name := "empty"
    memory := .sbuf
    parSize := 0
    freeSize := 0
  }

end Address

/--
TensorName represents a tensor at runtime. Each runtime tensor has a dtype,
shape, and address. The address size must be large enough to hold the tensor.
Unlike a TensorSram or TensorHbm, a TensorName may not yet have an address
assigned, or it may not have its final access pattern computed.
-/
@[serde tag = 114]
structure TensorName where
  name    : String
  dtype   : Dtype
  shape   : Shape
  address : Address
  freeElements : Nat := shape.freeElements
  parWF   : shape.parDim <= address.parSize
  freeWF  : shape.freeElements * dtype.size <= address.freeSize
  deriving Repr

instance : BEq TensorName where
  beq l r := l.name == r.name &&
             l.dtype == r.dtype &&
             l.shape == r.shape &&
             l.address == r.address

-- TODO
instance : FromJson TensorName := ⟨ fun _ => throw "" ⟩
instance : FromSexp TensorName := ⟨ fun _ => throw "" ⟩
instance : ToSexp TensorName := ⟨ fun _ => default ⟩
instance : ToJson TensorName := ⟨ fun _ => default ⟩

namespace TensorName

-- TODO: should .mk be private?
def make (name : String)
         (dtype : Dtype)
         (shape : Shape)
         (addr : Option Address) : Err TensorName := do
  let addr := addr.getD (Address.withDefaultSize default shape dtype)
  if parWF : shape.parDim <= addr.parSize then
    if freeWF : shape.freeElements * dtype.size <= addr.freeSize then
      return ⟨ name, dtype, shape, addr, shape.freeElements, parWF, freeWF ⟩
  throw "Tensor does not fit within memory location"

def withShape (name : TensorName) (shape : Shape) : Err TensorName :=
  make name.name name.dtype shape (name.address.withDefaultSize shape name.dtype)

-- NOTE: The Prop fields count towards the list, but have zero size
instance : ToCBOR TensorName where
  toCBOR t :=
    Serde.cborTag 114 0 7
    ++ @Serde.toCBOR String _ t.name
    ++ @Serde.toCBOR Dtype _ t.dtype
    ++ @Serde.toCBOR Shape _ t.shape
    ++ @Serde.toCBOR Address _ t.address
    ++ @Serde.toCBOR Nat _ t.freeElements

instance : FromCBOR TensorName where
  parse arr := do
    let (ty,val,len,arr) <- Serde.parseCBORTag arr
    if ty != 114 then
      throw s!"expecting TensorSRam (got tag {ty})"
    if val != 0 then
      throw s!"expecting TensorSRam (got val tag {val})"
    if len != 7 then
      throw s!"expecting TensorSRam (got len {len})"
    let (arr, sz, name) <- @Serde.parseCBOR' String _ arr 4
    let (arr, sz, dtype) <- @Serde.parseCBOR' Dtype _ arr sz
    let (arr, sz, shape) <- @Serde.parseCBOR' Shape _ arr sz
    let (arr, sz, address) <- @Serde.parseCBOR' Address _ arr sz
    let (_, sz, _) <- @Serde.parseCBOR' Nat _ arr sz
    let t <- make name dtype shape address
    return (sz, t)

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
@[serde tag = 115]
structure Slice where
  l : Nat
  u : Nat
  step : Int
  wf : step ≠ 0
  deriving BEq, Repr

-- TODO
instance : FromJson Slice := ⟨ fun _ => throw "" ⟩
instance : FromSexp Slice := ⟨ fun _ => throw "" ⟩
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

-- NOTE: The Prop fields count towards the list, but have zero size
instance : ToCBOR Slice where
  toCBOR t :=
    Serde.cborTag 115 0 4
    ++ @Serde.toCBOR Nat _ t.l
    ++ @Serde.toCBOR Nat _ t.u
    ++ @Serde.toCBOR Int _ t.step

instance : FromCBOR Slice where
  parse arr := do
    let (ty,val,len,arr) <- Serde.parseCBORTag arr
    if ty != 115 then
      throw s!"expecting Slice (got tag {ty})"
    if val != 0 then
      throw s!"expecting Slice (got val tag {val})"
    if len != 4 then
      throw s!"expecting Slice (got len {len})"
    let (arr, sz, l) <- @Serde.parseCBOR' Nat _ arr 4
    let (arr, sz, u) <- @Serde.parseCBOR' Nat _ arr sz
    let (_, sz, step) <- @Serde.parseCBOR' Int _ arr sz
    let s <- make l u step
    return (sz, s)

end Slice

@[serde tag = 117]
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

@[serde tag = 118]
structure AccessBasic where
  tensor : TensorName
  indexes : List Index
  lenWF : tensor.shape.freeDims.length + 1 = indexes.length
  deriving Repr

instance : BEq AccessBasic where
  beq l r := l.tensor == r.tensor && l.indexes == r.indexes

-- TODO
instance : FromJson AccessBasic := ⟨ fun _ => throw "" ⟩
instance : FromSexp AccessBasic := ⟨ fun _ => throw "" ⟩
instance : ToSexp AccessBasic := ⟨ fun _ => default ⟩
instance : ToJson AccessBasic := ⟨ fun _ => default ⟩

namespace AccessBasic

def make (t : TensorName) (i : List Index) : Err AccessBasic := do
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

-- NOTE: The Prop fields count towards the list, but have zero size
instance : ToCBOR AccessBasic where
  toCBOR t :=
    Serde.cborTag 118 0 3
    ++ @Serde.toCBOR TensorName _ t.tensor
    ++ @Serde.toCBOR (List Index) _ t.indexes

instance : FromCBOR AccessBasic where
  parse arr := do
    let (ty,val,len,arr) <- Serde.parseCBORTag arr
    if ty != 118 then
      throw s!"expecting AccessBasic (got tag {ty})"
    if val != 0 then
      throw s!"expecting AccessBasic (got val tag {val})"
    if len != 3 then
      throw s!"expecting AccessBasic (got len {len})"
    let (arr, sz, tensor) <- @Serde.parseCBOR' TensorName _ arr 4
    let (_, sz, indexes) <- @Serde.parseCBOR' (List Index) _ arr sz
    let acc <- make tensor indexes
    return (sz, acc)

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
@[serde tag = 119]
structure APPair where
  step : Int := 1
  num : Nat := 1
  deriving Inhabited, BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

def accessSize (pairs : List APPair) : Nat :=
  pairs.foldl (fun acc p => acc * p.num) 1

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

@[serde tag = 120]
structure AccessPattern where
  tensor : TensorName
  parNum : Nat
  freePattern : List APPair
  parOffset : Nat := 0
  freeOffset : Nat := 0
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace AccessPattern

def shape (ap : AccessPattern) : Shape :=
  .mk ap.parNum $ ap.freePattern.map fun pair => pair.num

-- Partitions are not counted in bytes or elements; I'll call them logical "rows".
def partitionRowOffset (ap : AccessPattern) : Nat :=
  ap.tensor.address.parOffset.getD 0 + ap.parOffset

def freeByteOffset (ap : AccessPattern) : Nat :=
  ap.tensor.address.freeOffset.getD 0 + ap.freeOffset

-- We can't find documentation that the free offset must be aligned by dtype size, but we think
-- it's probably the case. It certainly makes calculating indexes easier so we're going with it
-- for now.
def freeElementOffset (ap : AccessPattern) : Nat :=
  ap.freeByteOffset / ap.tensor.dtype.size

end AccessPattern

/-
BIR compatible access patterns

These are similar to the AccessPatterns, but the partition and free dimensions
are combined. In addition, unlike AccessPatterns, the offset is interpreted as
though the entire tensor is layed out in contiguous row-major form.

After allocation, the physical offset can be computed by (pseudo code):

  freeElements := pattern.tail.freeElements
  parOffset = floor (offset / freeElements) + address.parOffset
  freeOffset = offset % freeElements + address.freeOffset
  physicalOffset = parOffset * parSize + freeOffset * dtype.size
-/


mutual

@[serde tag = 123]
inductive ScalarOffset where
  | reg (r : String)
  | acc (a : Access)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 124]
structure BirAccessPattern where
  tensor : TensorName
  offset : Nat
  pattern : List APPair
  scalarOffset : Option ScalarOffset
  vectorOffset : Option Access
  indirectDim : Int
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp


-- Tensor access: whole tensor (simple), basic indexing, or access pattern
-- TODO: add advanced indexing (tensor indirect) inductive Access where
@[serde tag = 125]
inductive Access where
  | simple  (tensor : TensorName)
  | basic   (access : AccessBasic)
  | pattern (access : AccessPattern)
  | birPattern (access : BirAccessPattern)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
end

namespace BirAccessPattern

def shape (bap : BirAccessPattern) : Shape :=
  match bap.pattern with
  | [] => .mk 0 []
  | ⟨ _, parNum ⟩ :: rest => .mk parNum $ rest.map fun pair => pair.num

def fromAccessPattern (ap : AccessPattern) : BirAccessPattern :=
  let free := ap.tensor.shape.freeElements
  { tensor := ap.tensor
    offset := free * ap.parOffset + ap.freeOffset
    pattern := ⟨ free, ap.parNum ⟩ :: ap.freePattern
    scalarOffset := none
    vectorOffset := none
    indirectDim := 0
  }
end BirAccessPattern

namespace Access

def mkBasic (t : TensorName) (i : List Index) : Err Access :=
  return .basic (<- AccessBasic.make t i)

def tensor : Access -> TensorName
  | simple tensor
  | basic {tensor, ..}
  | pattern {tensor, ..} => tensor
  | birPattern {tensor, ..} => tensor

def shape : Access -> Err Shape
  | .simple t => return t.shape
  | .basic b => b.shape
  | .pattern ap => return ap.shape
  | .birPattern bap => return bap.shape

theorem shape.noFail :
  forall (a : Access), Access.shape a ≠ Except.error s := by
  unfold Access.shape pure
  unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold Except.instMonad Except.pure
  intro a
  cases a <;> simp
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
@[serde tag = 126]
structure TensorHbm where
  name : String
  dtype   : Dtype
  address : Nat
  dims : List APPair
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace TensorHbm
def fromAccessPattern (ap : AccessPattern) : Err TensorHbm := do
  let parOffset <-
    match ap.tensor.address.parOffset with
    | some n => pure (n + ap.parOffset)
    | none => throw "Attempt to convert unallocated address"
  let freeOffset <-
    match ap.tensor.address.freeOffset with
    | some n => pure (n + ap.freeOffset)
    | none => throw "Attempt to convert unallocated address"
  return {
     name := ap.tensor.name
     dtype := ap.tensor.dtype
     address := parOffset * ap.tensor.shape.freeElements + freeOffset
     dims := ⟨ 1, ap.parNum ⟩ :: ap.freePattern
   }

end TensorHbm

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
@[serde tag = 127]
structure TensorSram where
  name : String
  dtype : Dtype
  -- The size of this tensor in the parallel dimension
  parNum : Nat
  -- The length and stride of each dimension besides the first
  freePattern: List APPair
  -- Which parallel dimension channel this tensor starts at
  parOffset : Nat := 0
  -- The offset in the partition channel of this tensor
  freeOffset : Nat := 0
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace TensorSram

def fromAccessPattern (ap : AccessPattern) : Err TensorSram := do
  let parOffset <-
    match ap.tensor.address.parOffset with
    | some n => pure (n + ap.parOffset)
    | none => throw "Attempt to convert unallocated address"
  let freeOffset <-
    match ap.tensor.address.freeOffset with
    | some n => pure (n + ap.freeOffset)
    | none => throw "Attempt to convert unallocated address"
  return {
     name := ap.tensor.name
     dtype := ap.tensor.dtype
     parNum := ap.parNum
     freePattern := ap.freePattern
     parOffset
     freeOffset
   }

end TensorSram

/-
The type that is passed to instructions to refer to a tensor in SBUF. We abstract
over whether the tensor is a literal or stored in a shape register.
-/
@[serde tag = 128]
inductive TensorRef where
  | abstract (access : Access)
  | sbuf (view : TensorSram)
  | psum (view : TensorSram)
  | hbm (view : TensorHbm)
  | register (reg : Reg)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
