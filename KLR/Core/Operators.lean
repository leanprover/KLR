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
import Lean

/-
# Definition of operators

These definitions follow the hardware ISA as close as possible.
-/
namespace KLR.Core
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

-- Compute Engines
@[serde tag = 130]
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 131]
inductive Immediate where
  | register (reg : Reg)
  | pointer -- TODO
  | int (i : Int32)
  | float (f : Float32)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 132]
inductive ActivationImm where
  | register (reg : Reg)
  | pointer -- : TODO
  | float (f : Float32)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
Used for Iota and AffineSelect, represents something similar to an
TensorSram but that is only used to generate data, not to index. Much like
LEA in x86.
-/
@[serde tag = 133]
structure DataPattern where
  offset  : Nat
  pattern  : List APPair
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
ALU operations supported by the HW
Only used by: TensorScalar, TensorScalarPtr, TensorReduce, TensorTensor
-/
@[serde tag = 134]
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

/-- The ALUOps for a TensorReduceArithOp -/
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
@[serde tag = 135]
inductive DropoutThresholdType
  | DropRate
  | KeepRate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Control how data is accumulated at destination locations -/
@[serde tag = 136]
inductive AccumCmd where
  | Idle
  | Zero
  | Accumulate
  | ZeroAccumulate
  | LoadAccumulate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 137]
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
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- The comparator for an affine select -/
@[serde tag = 138]
inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- RMW ops for DMA -/
@[serde tag = 139]
inductive DgeComputeOp where
  | none
  | add
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- The DMA bounds check flag can either be an immediate or in a register -/
@[serde tag = 140]
inductive DmaBounds where
  | disable
  | enable
  | reg (reg : Reg)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Indicates whether this is the first, middle, or last matmul
instruction in a series of instructions that are accumulating into a region
of psum -/
@[serde tag = 141]
inductive MatmulGroupElement where
  | first
  | middle
  | last
  | whole
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Whether an immediate should be written, or nothing should be written, when an index misses -/
@[serde tag = 142]
inductive IndexMissBehavior where
  | imm (value : Immediate)
  | skip
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Which of the ops to TensorScalar should be reversed (only matters for
non-commutative operators)-/
@[serde tag = 143]
inductive TensorScalarReverseOps where
  | none
  | first
  | second
  | both
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- A representation of a contiguous set of axes of a tensor -/
@[serde tag = 144]
inductive TensorSubDim where
  | X
  | XY
  | XYZ
  | XYZW
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

def TensorSubDim.IsCopySubDim : TensorSubDim → Prop
| X => True | _ => False

/- Dropout instruction -/
@[serde tag = 145]
structure Dropout where
  dst           : TensorRef
  src           : TensorRef
  thresholdType : DropoutThresholdType
  threshold     : Immediate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Activate instruction

Performs the operation
`OUT accum= activate_func( (IN * scale_value) + bias, imm )`
-/
@[serde tag = 146]
structure Activate where
  dst             : TensorRef
  src             : TensorRef
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Immediate
  bias            : Immediate
  imm             : Immediate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- AffineSelect instruction

Generates values using the `maskPattern` and runs them through `op`. If
the comparison is true, the value from `in` is used, otherwise `fill_value` is used.
out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
-/
@[serde tag = 147]
structure AffineSelect where
  dst         : TensorRef
  src         : TensorRef
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- DmaCopy instruction

Generate descriptors to use the DMA to perform a copy. This is only used
for sbuf/psum transfers. For interacting with the HBM, use DmaHbmLoad/Store

TODO: this operation is stateful since it uses the DMA queues. How
do we represent that at the KLR level?
-/
@[serde tag = 148]
structure DmaCopy where
  dst            : TensorRef
  src            : TensorRef
  compute_op     : DgeComputeOp
  dstBoundsCheck : DmaBounds
  srcBoundsCheck : DmaBounds
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- DmaTranspose instruction
Use the DMA to reverse the dimensions of a tensor.
-/
@[serde tag = 149]
structure DmaTranspose where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Transpose Instruction

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.
-/
@[serde tag = 150]
structure Transpose where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- LoadMaskRegister instruction

Sets a register to be the MaskRegister in the DVE
-/
@[serde tag = 151]
structure LoadMaskRegister where
  regNum : Reg
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
Use the DVE to shuffle the data in src into dst based on MaskRegister
-/
@[serde tag = 152]
structure Shuffle where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- MemSet instruction

Sets `count` elements of `dst` to `value`
-/
@[serde tag = 153]
structure MemSet where
  dst   : TensorRef
  value : Immediate
  count : Nat
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Iota Instruction
Generates values using `pattern` and writes them to `dst` -/
@[serde tag = 154]
structure Iota where
  dst : TensorRef
  pattern : DataPattern
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- LoadStationary Instruction

Loads a matrix into the PE.
-/
@[serde tag = 155]
structure LoadStationary where
  src         : TensorRef
  isTranspose : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- MatMul instruction

Performs a matmul against the currently loaded tensor using the PE -/
@[serde tag = 156]
structure MatMul where
  dst                : TensorRef
  moving             : TensorRef
  psumAccumulateFlag : MatmulGroupElement
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- LocalGather instruction
-/
@[serde tag = 157]
structure LocalGather where
  dst               : TensorRef
  src               : TensorRef
  indexMissBehavior : IndexMissBehavior
  /- Set to true when this is the last local gather operation in a group
  to free the pool buffer -/
  freePoolBuffer    : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- RangeSelect instruction
-/
@[serde tag = 158]
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
@[serde tag = 159]
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

/- CopyPredicated instruction

Copies each element from src to dst for which predicate is not 0 -/
@[serde tag = 160]
structure CopyPredicated where
  dst       : TensorRef
  src       : TensorRef
  predicate : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- TensorTensorScan instruction

for lane_id in range(num_active_channels):
    internal_state = imm0
    for src0_elem, src1_elem in packed(src0_mem_pattern, src1_mem_pattern):
        new_result = (src0_elem op0 internal_state) op1 src1_elem
        internal_state = new_result
        dst_mem_pattern.append(new_result)
-/
@[serde tag = 161]
structure TensorTensorScan where
  dst             : TensorRef
  src0            : TensorRef
  src1            : TensorRef
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- MatchValueLoad instruction

Loads values into the DVE's MatchValue registers -/
@[serde tag = 162]
structure MatchValueLoad where
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp


/- FindIndex8 instruction

For each element in MatchValue register, find the first element of src that
matches and stores its index in dst. -/
@[serde tag = 163]
structure FindIndex8 where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- MatchReplace8 instruction

Same as FindIndex8, but replaces the found values in src with `replaceValue`-/
@[serde tag = 164]
structure MatchReplace8 where
  dst          : TensorRef
  src          : TensorRef
  replaceValue : Immediate
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Max8 instruction

Finds the 8 largest values in src and writes them to dst -/
@[serde tag = 165]
structure Max8 where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- BatchNormAggregate instruction
-/
@[serde tag = 166]
structure BatchNormAggregate where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- BatchNormStats instruction
-/
@[serde tag = 167]
structure BatchNormStats where
  dst : TensorRef
  src : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Reciprocal instruction
-/
@[serde tag = 168]
structure Reciprocal where
  dst  : TensorRef
  src  : TensorRef
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- Copy instruction
Copy src to dst -/
@[serde tag = 169]
structure Copy where
  dst   : TensorRef
  src   : TensorRef
  /- TODO: what is this for? -/
  opDim : Option TensorSubDim
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- TensorReduce instruction

Reduces a tensor along specified dimensions -/
@[serde tag = 170]
structure TensorReduce where
  dst          : TensorRef
  src          : TensorRef
  op           : AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- TensorScalar instruction

output[k] = (input[k] <op0> imm0) <op1> imm1
-/
@[serde tag = 171]
structure TensorScalar where
  dst : TensorRef
  src : TensorRef
  imm0 : Immediate
  op0 : AluOp
  imm1 : Immediate
  op1 : AluOp
  reverse : TensorScalarReverseOps
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/- TensorTensor instruction
-/
@[serde tag = 172]
structure TensorTensor where
  dst : TensorRef
  src0 : TensorRef
  src1 : TensorRef
  op : AluOp
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 173]
inductive Operator where
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
