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

import KLR.Core.Tensor
import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util

/-
# Definition of operators

These definitions follow the hardware ISA as close as possible.
-/
namespace KLR.Core
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

@[serde tag = 129]
inductive MatmulPerfMode where
  | None
  | DoubleRow
  | DoubleRowSwInterleave
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp


-- Compute Engines
@[serde tag = 130]
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 132]
inductive ActivationImm where
  | register (reg : Reg)
  | pointer -- : TODO
  | float (f : Float32)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 133]
inductive Operand where
  | imm (i : Immediate)
  | tile (t : TensorRef)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-! ## MapTensorRefs typeclass for generic tensor traversal -/

class MapTensorRefs (α : Type) where
  mapM {m : Type → Type} [Monad m] : (TensorRef → m TensorRef) → (Operand → m Operand) → α → m α

export MapTensorRefs (mapM)

instance : MapTensorRefs Operand where
  mapM _ fo op := fo op

instance : MapTensorRefs TensorRef where
  mapM ft _ t := ft t

instance [MapTensorRefs α] : MapTensorRefs (Option α) where
  mapM ft fo opt := opt.mapM (MapTensorRefs.mapM ft fo)

instance [MapTensorRefs α] : MapTensorRefs (List α) where
  mapM ft fo l := l.mapM (MapTensorRefs.mapM ft fo)

/-
Used for Iota and AffineSelect, represents something similar to an
TensorSram but that is only used to generate data, not to index. Much like
LEA in x86.
-/
@[serde tag = 134]
structure DataPattern where
  offset  : Int
  pattern  : List APPair
  channelMultiplier : Int
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
ALU operations supported by the HW
Only used by: TensorScalar, TensorScalarPtr, TensorReduce, TensorTensor
-/
@[serde tag = 135]
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
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

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

-- TODO: Why do we need both Bool and Prop?
-- TODO: can this just be isArith x == true ?
def IsArith : AluOp → Prop
| .abs | .add | .average | .bypass | .divide | .is_equal | .is_ge | .is_gt | .is_le | .is_lt | .max | .min | .mod | .mult | .not_equal | .pow | .rsqrt | .subtract => True
| _ => False

def IsTensorReduceArithOp : AluOp → Prop
| abs | add | average | bypass | is_equal | is_ge | is_gt | is_le | is_lt | max | min | mult | not_equal | subtract => True
| _ => False

/-- The ALUOps for a TensorReduceBitvecOp -/
def IsTensorReduceBitwiseOp : AluOp → Prop
| arith_shift_left | arith_shift_right | bitwise_and | bitwise_or | bitwise_xor | logical_and | logical_or | logical_shift_left | logical_shift_right | logical_xor => True
| _ => False

instance : ToString AluOp where
  toString op := reprStr op

end AluOp

/- Whether the dropout rate is how many values should be dropped or how many
values should be kept -/
@[serde tag = 136]
inductive DropoutThresholdType
  | DropRate
  | KeepRate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Control how data is accumulated at destination locations -/
@[serde tag = 137]
inductive AccumCmd where
  | Idle
  | Zero
  | Accumulate
  | ZeroAccumulate
  | LoadAccumulate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 138]
inductive ActivationFunc where
  | abs
  | arctan
  | copy
  | erf
  | erf_dx
  | exp
  | gelu
  | gelu_apprx_tanh
  | gelu_dx
  | log
  | mish
  | reciprocal
  | relu
  | rsqrt
  | sigmoid
  | sign
  | silu
  | silu_dx
  | sin
  | softplus
  | sqrt
  | square
  | tanh
  | gelu_apprx_sigmoid
  | gelu_apprx_sigmoid_dx
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- The comparator for an affine select -/
@[serde tag = 139]
inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- RMW ops for DMA -/
@[serde tag = 140]
inductive DgeComputeOp where
  | none
  | add
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- The DMA bounds check flag can either be an immediate or in a register -/
@[serde tag = 141]
inductive DmaBounds where
  | skip
  | error
  | reg (reg : Reg)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Indicates whether this is the first, middle, or last matmul
instruction in a series of instructions that are accumulating into a region
of psum -/
@[serde tag = 142]
inductive MatmulGroupElement where
  | first
  | middle
  | last
  | whole
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Whether an immediate should be written, or nothing should be written, when an index misses -/
@[serde tag = 143]
inductive IndexMissBehavior where
  | imm (value : Immediate)
  | skip
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Which of the ops to TensorScalar should be reversed (only matters for
non-commutative operators)-/
@[serde tag = 144]
inductive TensorScalarReverseOps where
  | none
  | first
  | second
  | both
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- A representation of a contiguous set of axes of a tensor -/
@[serde tag = 145]
inductive TensorSubDim where
  | X
  | XY
  | XYZ
  | XYZW
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 146]
inductive TransposeOps where
  | None
  | WZXY
  | WXZY
  | WYXZ
  | ZWYX
  | ZYWX
  | ZYXW
  | YXWZ
  | YXZW
  | YWZX
  | XWZY
  | XZYW
  | XYZW
  | XYWZ
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

def TensorSubDim.IsCopySubDim : TensorSubDim → Prop
| X => True | _ => False

@[serde tag = 147]
structure Dropout where
  dst           : TensorRef
  src           : TensorRef
  thresholdType : DropoutThresholdType
  threshold     : Operand
  dtype         : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Dropout where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, threshold := ← fo op.threshold }

/- Activate instruction

Performs the operation
`OUT accum= activate_func( (IN * scale_value) + bias, imm )`
-/
@[serde tag = 148]
structure Activate where
  dst             : TensorRef
  src             : TensorRef
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Immediate
  bias            : Immediate
  imm             : Immediate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Activate where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 149]
structure NcActivate where
  dst             : TensorRef
  src             : TensorRef
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Operand
  bias            : Option TensorRef
  reduceOp        : Option AluOp
  reduceRes       : Option TensorRef
  dtype           : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcActivate where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, scale := ← fo op.scale, bias := ← op.bias.mapM ft, reduceRes := ← op.reduceRes.mapM ft }

/- AffineSelect instruction

Generates values using the `maskPattern` and runs them through `op`. If
the comparison is true, the value from `in` is used, otherwise `fill_value` is used.
out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
-/
@[serde tag = 150]
structure AffineSelect where
  dst         : TensorRef
  src         : TensorRef
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs AffineSelect where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 151]
structure NcAffineSelect where
  dst          : TensorRef
  pred         : DataPattern
  onTrueTile   : TensorRef
  onFalseValue : Immediate
  dtype        : Option Dtype
  cmpOp        : AluOp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcAffineSelect where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, onTrueTile := ← ft op.onTrueTile }

/- DmaCopy instruction

Generate descriptors to use the DMA to perform a copy. This is only used
for sbuf/psum transfers. For interacting with the HBM, use DmaHbmLoad/Store

TODO: this operation is stateful since it uses the DMA queues. How
do we represent that at the KLR level?
-/
@[serde tag = 152]
structure DmaCopy where
  dst            : TensorRef
  src            : TensorRef
  compute_op     : DgeComputeOp
  dstBoundsCheck : DmaBounds
  srcBoundsCheck : DmaBounds
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs DmaCopy where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 153]
structure NcDmaCopy where
  dst                : TensorRef
  src                : TensorRef
  compute_op         : DgeComputeOp
  oobMode            : DmaBounds
  dgeMode            : Nat
  uniqueIndices      : Bool
  engine             : Engine
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcDmaCopy where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- DmaTranspose instruction
Use the DMA to reverse the dimensions of a tensor.
-/
@[serde tag = 154]
structure DmaTranspose where
  dst : TensorRef
  src : TensorRef
  axes : TransposeOps
  dtype : Option Dtype
  dgeMode : Nat
  oobMode : DmaBounds
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs DmaTranspose where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- Transpose Instruction

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.
-/
@[serde tag = 155]
structure Transpose where
  dst : TensorRef
  src : TensorRef
  dtype : Option Dtype
  engine : Engine
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Transpose where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- LoadMaskRegister instruction

Sets a register to be the MaskRegister in the DVE
-/
@[serde tag = 156]
structure LoadMaskRegister where
  regNum : Reg
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs LoadMaskRegister where
  mapM _ _ op := pure op

/-
Use the DVE to shuffle the data in src into dst based on MaskRegister
-/
@[serde tag = 157]
structure Shuffle where
  dst : TensorRef
  src : TensorRef
  shuffleMask : List Immediate
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Shuffle where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- MemSet instruction

Sets `count` elements of `dst` to `value`
-/
@[serde tag = 158]
structure MemSet where
  dst   : TensorRef
  value : Immediate
  dtype  : Dtype
  engine : Engine
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs MemSet where
  mapM ft _ op := do pure { op with dst := ← ft op.dst }

/- Iota Instruction
Generates values using `pattern` and writes them to `dst` -/
@[serde tag = 159]
structure Iota where
  dst : TensorRef
  pattern : DataPattern
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Iota where
  mapM ft _ op := do pure { op with dst := ← ft op.dst }

/- LoadStationary Instruction

Loads a matrix into the PE.
-/
@[serde tag = 160]
structure LoadStationary where
  src         : TensorRef
  isTranspose : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs LoadStationary where
  mapM ft _ op := do pure { op with src := ← ft op.src }

/- MatMul instruction

Performs a matmul against the currently loaded tensor using the PE -/
@[serde tag = 161]
structure MatMul where
  dst                : TensorRef
  moving             : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs MatMul where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, moving := ← ft op.moving }

/- LocalGather instruction
-/
@[serde tag = 162]
structure LocalGather where
  dst               : TensorRef
  src               : TensorRef
  indexMissBehavior : IndexMissBehavior
  /- Set to true when this is the last local gather operation in a group
  to free the pool buffer -/
  freePoolBuffer    : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs LocalGather where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 163]
structure NcLocalGather where
  dst               : TensorRef
  src               : TensorRef
  index             : TensorRef
  numElemPerIdx     : Immediate
  numValidIndicies  : Option Immediate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcLocalGather where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, index := ← ft op.index }

/- RangeSelect instruction
-/
@[serde tag = 164]
structure RangeSelect where
  dst            : TensorRef
  src            : TensorRef
  reduceCommand  : AccumCmd
  reduceOp       : AluOp
  base           : Float32
  fillValue      : Float32
  compOp0        : AluOp
  compOp1        : AluOp
  bound0         : Immediate
  bound1         : Immediate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs RangeSelect where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 165]
structure NcRangeSelect where
  dst            : TensorRef
  reduceCommand  : AccumCmd
  reduceRes      : Option TensorRef
  reduceOp       : Option AluOp
  compOp0        : AluOp
  compOp1        : AluOp
  bound0         : TensorRef
  bound1         : TensorRef
  rangeStart     : Immediate
  onTrueTile     : TensorRef
  onFalseValue   : Immediate
  dtype          : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcRangeSelect where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, reduceRes := ← op.reduceRes.mapM ft, bound0 := ← ft op.bound0, bound1 := ← ft op.bound1, onTrueTile := ← ft op.onTrueTile }

/- ScalarTensorTensor instruction

```
if accumulator_cmd == ZeroAccumulator:
    accum_value = 0
scalar_result = src0 op_0 imm0 # broadcast imm0 onto src0
dst = scalar_result op_1 src1
if (accumulator_cmd == ZeroAccumulator) or (accumulator_cmd == Accumulator):
    accum_value += dst
```
-/
@[serde tag = 166]
structure ScalarTensorTensor where
  dst             : TensorRef
  src0            : TensorRef
  src1            : TensorRef
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs ScalarTensorTensor where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src0 := ← ft op.src0, src1 := ← ft op.src1 }

@[serde tag = 167]
structure NcScalarTensorTensor where
  dst             : TensorRef
  data            : TensorRef
  src0            : Operand
  src1            : Operand
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  dtype           : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcScalarTensorTensor where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, data := ← ft op.data, src0 := ← fo op.src0, src1 := ← fo op.src1 }

/- CopyPredicated instruction

Copies each element from src to dst for which predicate is not 0 -/
@[serde tag = 168]
structure CopyPredicated where
  dst       : TensorRef
  src       : TensorRef
  predicate : TensorRef
  dtype       : Option Dtype
  reversePred : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs CopyPredicated where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, predicate := ← ft op.predicate }

/- TensorTensorScan instruction

for lane_id in range(num_active_channels):
    internal_state = imm0
    for src0_elem, src1_elem in packed(src0_mem_pattern, src1_mem_pattern):
        new_result = (src0_elem op0 internal_state) op1 src1_elem
        internal_state = new_result
        dst_mem_pattern.append(new_result)
-/
@[serde tag = 169]
structure TensorTensorScan where
  dst             : TensorRef
  src0            : TensorRef
  src1            : TensorRef
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Operand
  accumulatorCmd  : AccumCmd
  dtype           : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorTensorScan where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, src0 := ← ft op.src0, src1 := ← ft op.src1, imm0 := ← fo op.imm0 }

/- MatchValueLoad instruction

Loads values into the DVE's MatchValue registers -/
@[serde tag = 170]
structure MatchValueLoad where
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs MatchValueLoad where
  mapM ft _ op := do pure { op with src := ← ft op.src }

/- FindIndex8 instruction

For each element in MatchValue register, find the first element of src that
matches and stores its index in dst. -/
@[serde tag = 171]
structure FindIndex8 where
  dst : TensorRef
  src : TensorRef
  vals : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs FindIndex8 where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, vals := ← ft op.vals }

/- MatchReplace8 instruction

Same as FindIndex8, but replaces the found values in src with `replaceValue`-/
@[serde tag = 172]
structure MatchReplace8 where
  dst          : TensorRef
  src          : TensorRef
  vals         : TensorRef
  replaceValue : Immediate
  dstIdx       : Option TensorRef
  dtype        : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs MatchReplace8 where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, vals := ← ft op.vals, dstIdx := ← op.dstIdx.mapM ft }

/- Max8 instruction

Finds the 8 largest values in src and writes them to dst -/
@[serde tag = 173]
structure Max8 where
  dst : TensorRef
  src : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Max8 where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- BatchNormAggregate instruction
-/
@[serde tag = 174]
structure BatchNormAggregate where
  dst : TensorRef
  src : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs BatchNormAggregate where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- BatchNormStats instruction
-/
@[serde tag = 175]
structure BatchNormStats where
  dst : TensorRef
  src : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs BatchNormStats where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- Reciprocal instruction
-/
@[serde tag = 176]
structure Reciprocal where
  dst  : TensorRef
  src  : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Reciprocal where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- Copy instruction
Copy src to dst -/
@[serde tag = 177]
structure Copy where
  dst   : TensorRef
  src   : TensorRef
  /- TODO: what is this for? -/
  opDim : Option TensorSubDim
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Copy where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 178]
structure NcCopy where
  dst    : TensorRef
  src    : TensorRef
  dtype  : Option Dtype
  engine : Engine
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcCopy where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- TensorReduce instruction

Reduces a tensor along specified dimensions -/
@[serde tag = 179]
structure TensorReduce where
  dst          : TensorRef
  src          : TensorRef
  op           : AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool
  dtype        : Option Dtype
  keepdims     : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorReduce where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

/- TensorScalar instruction

output[k] = (input[k] <op0> imm0) <op1> imm1
-/
@[serde tag = 180]
structure TensorScalar where
  dst : TensorRef
  src : TensorRef
  imm0 : Operand
  op0 : AluOp
  imm1 : Option Operand
  op1 : Option AluOp
  reverse : TensorScalarReverseOps
  engine : Engine
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorScalar where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, imm0 := ← fo op.imm0, imm1 := ← op.imm1.mapM fo }

@[serde tag = 181]
structure TensorScalarReduce where
  dst : TensorRef
  src : TensorRef
  operand0 : Operand
  op0 : AluOp
  reverse0 : Bool
  dtype : Option Dtype
  reduceOp : Option AluOp
  reduceRes : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorScalarReduce where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, operand0 := ← fo op.operand0, reduceRes := ← ft op.reduceRes }

/- TensorTensor instruction
-/
@[serde tag = 182]
structure TensorTensor where
  dst : TensorRef
  src0 : TensorRef
  src1 : TensorRef
  op : AluOp
  dtype : Option Dtype
  engine : Engine
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorTensor where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src0 := ← ft op.src0, src1 := ← ft op.src1 }

@[serde tag = 183]
structure NcMatMul where
  dst : TensorRef
  stationary : TensorRef
  moving : TensorRef
  isStationaryOneZero : Bool
  isMovingZero : Bool
  isTranspose : Bool
  tilePosition : List Nat
  tileSize : List Nat
  perfMode : MatmulPerfMode
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcMatMul where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, stationary := ← ft op.stationary, moving := ← ft op.moving }

@[serde tag = 184]
structure TensorPartitionReduce where
  dst : TensorRef
  op : AluOp
  data : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorPartitionReduce where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, data := ← ft op.data }

@[serde tag = 185]
structure SelectReduce where
  dst : TensorRef
  predicate : TensorRef
  onTrue : TensorRef
  onFalse : Operand
  reduceRes : Option TensorRef
  reduceCmd: AccumCmd
  reduceOp : AluOp
  reversePred : Bool
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs SelectReduce where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, predicate := ← ft op.predicate, onTrue := ← ft op.onTrue, onFalse := ← fo op.onFalse, reduceRes := ← op.reduceRes.mapM ft }

@[serde tag = 186]
structure SequenceBounds where
  dst : TensorRef
  segmentIds : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs SequenceBounds where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, segmentIds := ← ft op.segmentIds }

@[serde tag = 187]
structure SendRecv where
  dst : TensorRef
  src : TensorRef
  sendToRank : Immediate
  recvFromRank : Immediate
  pipeId : Immediate
  useGpsimdDma : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs SendRecv where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src }

@[serde tag = 188]
structure SendRecvCCE where
  dst : TensorRef
  src : List TensorRef
  sendToRank : Immediate
  recvFromRanks : List Immediate
  pipeId : Immediate
  op : AluOp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs SendRecvCCE where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← op.src.mapM ft }

/-
Dynamic control flow operators
-/

@[serde tag = 189]
inductive BrCmpOp where
  | always
  | lt_imm | le_imm | eq_imm | ne_imm | ge_imm | gt_imm
  | lt_reg | le_reg | eq_reg | ne_reg | ge_reg | gt_reg
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 190]
structure TensorLoad where
  dst : String    -- register name
  src : TensorRef -- 1x1 tensor access
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorLoad where
  mapM ft _ op := do pure { op with src := ← ft op.src }

@[serde tag = 191]
structure TensorStore where
  dst : TensorRef -- 1x1 tensor access
  src : String    -- register name
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorStore where
  mapM ft _ op := do pure { op with dst := ← ft op.dst }

@[serde tag = 192]
structure RegisterMove where
  dst : String
  imm : Int32
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs RegisterMove where
  mapM _ _ op := pure op

@[serde tag = 193]
structure CmpBranch where
  reg1 : String
  reg2 : String
  imm : Int32
  op : BrCmpOp
  trueLabel : String
  falseLabel : String
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs CmpBranch where
  mapM _ _ op := pure op

@[serde tag = 194]
structure RegisterAluOp where
  dst : String
  src : String
  imm : Int32
  op : AluOp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs RegisterAluOp where
  mapM _ _ op := pure op

@[serde tag = 195]
structure QuantizeMX where
    dst :       TensorRef  -- NOTE: do we need special tensor types for MX ones. ISA does
    src :       TensorRef
    dstScale :  TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs QuantizeMX where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, dstScale := ← ft op.dstScale }

@[serde tag = 196]
structure MatMulMX where
    dst : TensorRef
    stationary : TensorRef
    moving : TensorRef
    stationaryScale : TensorRef
    movingScale : TensorRef
    tilePosition : Option (List Nat)
    tileSize : Option (List Nat)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs MatMulMX where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, stationary := ← ft op.stationary, moving := ← ft op.moving, stationaryScale := ← ft op.stationaryScale, movingScale := ← ft op.movingScale }

@[serde tag = 197]
structure DmaCompute where
    dst : TensorRef
    srcs : List TensorRef
    scales : List Immediate
    reduceOp : AluOp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs DmaCompute where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, srcs := ← op.srcs.mapM ft }

@[serde tag = 198]
structure CollectiveOp where
  dsts : List TensorRef
  srcs : List TensorRef
  op : Option AluOp
  replicaGroups : Option (List (List Int))
  reduceScatterDim : Option Int
  allGatherDim : Option Int
  sourceTargetPairs : Option (List (List Int))
  broacastSizes : Option (List Int)
  splitDim : Option Int
  concatDim : Option Int
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs CollectiveOp where
  mapM ft _ op := do pure { op with dsts := ← op.dsts.mapM ft, srcs := ← op.srcs.mapM ft }

@[serde tag = 199]
structure Send where
  op : AluOp
  srcs : List TensorRef
  peerId : Int
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Send where
  mapM ft _ op := do pure { op with srcs := ← op.srcs.mapM ft }

@[serde tag = 200]
structure Recv where
  op : AluOp
  dsts : List TensorRef
  replicaGroups : List Int
  peerId : Int
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Recv where
  mapM ft _ op := do pure { op with dsts := ← op.dsts.mapM ft }

@[serde tag = 201]
structure CoreBarrier where
  data : TensorRef
  cores : List Int
  engine : Engine
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs CoreBarrier where
  mapM ft _ op := do pure { op with data := ← ft op.data }

@[serde tag = 202]
structure Rng where
  dst : TensorRef
  engine : Engine
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Rng where
  mapM ft _ op := do pure { op with dst := ← ft op.dst }

@[serde tag = 203]
structure Rand2 where
  dst : TensorRef
  min : Operand
  max : Operand
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Rand2 where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, min := ← fo op.min, max := ← fo op.max }

@[serde tag = 204]
structure RandGetState where
  dst : TensorRef
  engine : Engine
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs RandGetState where
  mapM ft _ op := do pure { op with dst := ← ft op.dst }

-- trn1 and trn2
@[serde tag = 205]
structure SetRngSeed where
  src : TensorRef
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs SetRngSeed where
  mapM ft _ op := do pure { op with src := ← ft op.src }

-- trn2+
@[serde tag = 206]
structure RandSetState where
  src : TensorRef
  engine : Engine
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs RandSetState where
  mapM ft _ op := do pure { op with src := ← ft op.src }

@[serde tag = 207]
structure ExtendedInst where
  opcode : Nat
  hasRead : Bool
  hasWrite : Bool
  ports : Nat
  data0 : List Nat
  data1 : List Nat
deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs ExtendedInst where
  mapM _ _ op := pure op

@[serde tag = 208]
structure TensorScalarCumulative where
  dst : TensorRef
  src : TensorRef
  op0 : AluOp
  op1: AluOp
  imm0: Operand
  imm1: Option Operand
  reduceCmd: AccumCmd
  reverse : TensorScalarReverseOps
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs TensorScalarCumulative where
  mapM ft fo op := do pure { op with dst := ← ft op.dst, src := ← ft op.src, imm0 := ← fo op.imm0, imm1 := ← op.imm1.mapM fo }

@[serde tag = 209]
structure NcNGather where
  dst : TensorRef
  data : TensorRef
  indices : TensorRef
  dtype : Option Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs NcNGather where
  mapM ft _ op := do pure { op with dst := ← ft op.dst, data := ← ft op.data, indices := ← ft op.indices }

-- Device Print support
@[serde tag = 210]
inductive PrintOutputBuffer where
  | stdout | stderr
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

namespace PrintOutputBuffer
def toName (m : PrintOutputBuffer) :=
  match m with
  | .stdout => `stdout
  | .stderr => `stderr
end PrintOutputBuffer

@[serde tag = 211]
structure DevicePrint where
  src : TensorRef
  printPrefix : String
  buffer : PrintOutputBuffer
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs DevicePrint where
  mapM ft _ op := do pure { op with src := ← ft op.src }

@[serde tag = 212]
inductive Operator where
  | activate (op : Activate)
  | ncActivate (op : NcActivate)
  | activationReduce (op : NcActivate)
  | affineSelect (op : AffineSelect)
  | ncAffineSelect (op : NcAffineSelect)
  | batchNormAggregate (op : BatchNormAggregate)
  | batchNormStats (op : BatchNormStats)
  | copy (op : Copy)
  | ncCopy (op : NcCopy)
  | copyPredicated (op : CopyPredicated)
  | dmaCopy (op : DmaCopy)
  | ncDmaCopy (op : NcDmaCopy)
  | dmaTranspose (op : DmaTranspose)
  | dropout (op : Dropout)
  | findIndex8 (op : FindIndex8)
  | iota (op : Iota)
  | loadMaskRegister (op : LoadMaskRegister)
  | loadStationary (op : LoadStationary)
  | localGather (op : LocalGather)
  | ncLocalGather (op : NcLocalGather)
  | matMul (op : MatMul)
  | ncMatMul (op : NcMatMul)
  | matchReplace8 (op : MatchReplace8)
  | matchValueLoad (op : MatchValueLoad)
  | max8 (op : Max8)
  | memSet (op : MemSet)
  | rangeSelect (op : RangeSelect)
  | ncRangeSelect (op : NcRangeSelect)
  | reciprocal (op : Reciprocal)
  | scalarTensorTensor (op : ScalarTensorTensor)
  | ncScalarTensorTensor (op : NcScalarTensorTensor)
  | shuffle (op : Shuffle)
  | tensorReduce (op : TensorReduce)
  | tensorScalar (op : TensorScalar)
  | tensorTensor (op : TensorTensor)
  | tensorTensorScan (op : TensorTensorScan)
  | tensorPartitionReduce (op : TensorPartitionReduce)
  | tensorScalarReduce (op : TensorScalarReduce)
  | transpose (op : Transpose)
  | selectReduce (op : SelectReduce)
  | sequenceBounds (op : SequenceBounds)
  | sendRecv (op : SendRecv)
  | sendRecvCCE (op : SendRecvCCE)
  | tensorLoad (op : TensorLoad)
  | tensorStore (op : TensorStore)
  | registerMove (op : RegisterMove)
  | cmpBranch (op : CmpBranch)
  | registerAluOp (op : RegisterAluOp)
  | quantizeMX (op : QuantizeMX)
  | ncMatMulMX (op : MatMulMX)
  | dmaCompute (op : DmaCompute)
  | allReduce (op : CollectiveOp)
  | allGather (op : CollectiveOp)
  | reduceScatter (op : CollectiveOp)
  | collectivePermute (op : CollectiveOp)
  | broadcast (op : CollectiveOp)
  | allToAll (op : CollectiveOp)
  | send (op : Send)
  | recv (op : Recv)
  | coreBarrier (op : CoreBarrier)
  | rng (op : Rng)
  | rand2 (op : Rand2)
  | randGetState (op : RandGetState)
  | setRngSeed (op : SetRngSeed)
  | randSetState (op : RandSetState)
  | extendedInst (op : ExtendedInst)
  | tensorScalarCumulative (op: TensorScalarCumulative)
  | ncNGather (op: NcNGather)
  | devicePrint (op: DevicePrint)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 213]
inductive TGROperator where
  | activate (op : Activate)
  | affineSelect (op : AffineSelect)
  | batchNormAggregate (op : BatchNormAggregate)
  | batchNormStats (op : BatchNormStats)
  | copy (op : Copy)
  | copyPredicated (op : CopyPredicated)
  | dmaCopy (op : DmaCopy)
  | dmaTranspose (op : DmaTranspose)
  | dropout (op : Dropout)
  | findIndex8 (op : FindIndex8)
  | iota (op : Iota)
  | loadMaskRegister (op : LoadMaskRegister)
  | loadStationary (op : LoadStationary)
  | localGather (op : LocalGather)
  | matMul (op : MatMul)
  | matchReplace8 (op : MatchReplace8)
  | matchValueLoad (op : MatchValueLoad)
  | max8 (op : Max8)
  | memSet (op : MemSet)
  | rangeSelect (op : RangeSelect)
  | reciprocal (op : Reciprocal)
  | scalarTensorTensor (op : ScalarTensorTensor)
  | shuffle (op : Shuffle)
  | tensorReduce (op : TensorReduce)
  | tensorScalar (op : TensorScalar)
  | tensorTensor (op : TensorTensor)
  | tensorTensorScan (op : TensorTensorScan)
  | transpose (op : Transpose)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

instance : MapTensorRefs Operator where
  mapM ft fo
  | .activate op => return .activate (← MapTensorRefs.mapM ft fo op)
  | .ncActivate op => return .ncActivate (← MapTensorRefs.mapM ft fo op)
  | .activationReduce op => return .activationReduce (← MapTensorRefs.mapM ft fo op)
  | .affineSelect op => return .affineSelect (← MapTensorRefs.mapM ft fo op)
  | .ncAffineSelect op => return .ncAffineSelect (← MapTensorRefs.mapM ft fo op)
  | .batchNormAggregate op => return .batchNormAggregate (← MapTensorRefs.mapM ft fo op)
  | .batchNormStats op => return .batchNormStats (← MapTensorRefs.mapM ft fo op)
  | .copy op => return .copy (← MapTensorRefs.mapM ft fo op)
  | .ncCopy op => return .ncCopy (← MapTensorRefs.mapM ft fo op)
  | .copyPredicated op => return .copyPredicated (← MapTensorRefs.mapM ft fo op)
  | .dmaCopy op => return .dmaCopy (← MapTensorRefs.mapM ft fo op)
  | .ncDmaCopy op => return .ncDmaCopy (← MapTensorRefs.mapM ft fo op)
  | .dmaTranspose op => return .dmaTranspose (← MapTensorRefs.mapM ft fo op)
  | .dropout op => return .dropout (← MapTensorRefs.mapM ft fo op)
  | .findIndex8 op => return .findIndex8 (← MapTensorRefs.mapM ft fo op)
  | .iota op => return .iota (← MapTensorRefs.mapM ft fo op)
  | .loadMaskRegister op => return .loadMaskRegister (← MapTensorRefs.mapM ft fo op)
  | .loadStationary op => return .loadStationary (← MapTensorRefs.mapM ft fo op)
  | .localGather op => return .localGather (← MapTensorRefs.mapM ft fo op)
  | .ncLocalGather op => return .ncLocalGather (← MapTensorRefs.mapM ft fo op)
  | .matMul op => return .matMul (← MapTensorRefs.mapM ft fo op)
  | .ncMatMul op => return .ncMatMul (← MapTensorRefs.mapM ft fo op)
  | .matchReplace8 op => return .matchReplace8 (← MapTensorRefs.mapM ft fo op)
  | .matchValueLoad op => return .matchValueLoad (← MapTensorRefs.mapM ft fo op)
  | .max8 op => return .max8 (← MapTensorRefs.mapM ft fo op)
  | .memSet op => return .memSet (← MapTensorRefs.mapM ft fo op)
  | .rangeSelect op => return .rangeSelect (← MapTensorRefs.mapM ft fo op)
  | .ncRangeSelect op => return .ncRangeSelect (← MapTensorRefs.mapM ft fo op)
  | .reciprocal op => return .reciprocal (← MapTensorRefs.mapM ft fo op)
  | .scalarTensorTensor op => return .scalarTensorTensor (← MapTensorRefs.mapM ft fo op)
  | .ncScalarTensorTensor op => return .ncScalarTensorTensor (← MapTensorRefs.mapM ft fo op)
  | .shuffle op => return .shuffle (← MapTensorRefs.mapM ft fo op)
  | .tensorReduce op => return .tensorReduce (← MapTensorRefs.mapM ft fo op)
  | .tensorScalar op => return .tensorScalar (← MapTensorRefs.mapM ft fo op)
  | .tensorTensor op => return .tensorTensor (← MapTensorRefs.mapM ft fo op)
  | .tensorTensorScan op => return .tensorTensorScan (← MapTensorRefs.mapM ft fo op)
  | .tensorPartitionReduce op => return .tensorPartitionReduce (← MapTensorRefs.mapM ft fo op)
  | .tensorScalarReduce op => return .tensorScalarReduce (← MapTensorRefs.mapM ft fo op)
  | .transpose op => return .transpose (← MapTensorRefs.mapM ft fo op)
  | .selectReduce op => return .selectReduce (← MapTensorRefs.mapM ft fo op)
  | .sequenceBounds op => return .sequenceBounds (← MapTensorRefs.mapM ft fo op)
  | .sendRecv op => return .sendRecv (← MapTensorRefs.mapM ft fo op)
  | .sendRecvCCE op => return .sendRecvCCE (← MapTensorRefs.mapM ft fo op)
  | .tensorLoad op => return .tensorLoad (← MapTensorRefs.mapM ft fo op)
  | .tensorStore op => return .tensorStore (← MapTensorRefs.mapM ft fo op)
  | .registerMove op => return .registerMove (← MapTensorRefs.mapM ft fo op)
  | .cmpBranch op => return .cmpBranch (← MapTensorRefs.mapM ft fo op)
  | .registerAluOp op => return .registerAluOp (← MapTensorRefs.mapM ft fo op)
  | .quantizeMX op => return .quantizeMX (← MapTensorRefs.mapM ft fo op)
  | .ncMatMulMX op => return .ncMatMulMX (← MapTensorRefs.mapM ft fo op)
  | .dmaCompute op => return .dmaCompute (← MapTensorRefs.mapM ft fo op)
  | .allReduce op => return .allReduce (← MapTensorRefs.mapM ft fo op)
  | .allGather op => return .allGather (← MapTensorRefs.mapM ft fo op)
  | .reduceScatter op => return .reduceScatter (← MapTensorRefs.mapM ft fo op)
  | .collectivePermute op => return .collectivePermute (← MapTensorRefs.mapM ft fo op)
  | .broadcast op => return .broadcast (← MapTensorRefs.mapM ft fo op)
  | .allToAll op => return .allToAll (← MapTensorRefs.mapM ft fo op)
  | .send op => return .send (← MapTensorRefs.mapM ft fo op)
  | .recv op => return .recv (← MapTensorRefs.mapM ft fo op)
  | .coreBarrier op => return .coreBarrier (← MapTensorRefs.mapM ft fo op)
  | .rng op => return .rng (← MapTensorRefs.mapM ft fo op)
  | .rand2 op => return .rand2 (← MapTensorRefs.mapM ft fo op)
  | .randGetState op => return .randGetState (← MapTensorRefs.mapM ft fo op)
  | .setRngSeed op => return .setRngSeed (← MapTensorRefs.mapM ft fo op)
  | .randSetState op => return .randSetState (← MapTensorRefs.mapM ft fo op)
  | .extendedInst op => return .extendedInst (← MapTensorRefs.mapM ft fo op)
  | .tensorScalarCumulative op => return .tensorScalarCumulative (← MapTensorRefs.mapM ft fo op)
  | .ncNGather op => return .ncNGather (← MapTensorRefs.mapM ft fo op)
  | .devicePrint op => return .devicePrint (← MapTensorRefs.mapM ft fo op)
