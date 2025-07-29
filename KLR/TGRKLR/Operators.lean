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
namespace KLR.TGRKLR
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

-- Compute Engines
@[serde tag = 130]
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq

def VectorVar := String
deriving BEq, Inhabited, Repr, Nonempty, FromCBOR, ToCBOR, FromJson, ToJson, FromSexp, ToSexp

def Reg := Nat
deriving BEq, Inhabited, Repr, Nonempty, FromCBOR, ToCBOR, FromJson, ToJson, FromSexp, ToSexp

@[serde tag = 131]
inductive Immediate where
  | register (reg : Reg)
  | vector (vec : VectorVar)
  | pointer -- TODO
  | int (i : Int32)
  | float (f : Float32)
  deriving BEq

@[serde tag = 132]
inductive ActivationImm where
  | register (reg : Reg)
  | pointer -- : TODO
  | float (f : Float32)
  deriving BEq

/-
Used for Iota and AffineSelect, represents something similar to an
TensorSram but that is only used to generate data, not to index. Much like
LEA in x86.
-/
@[serde tag = 133]
structure DataPattern where
  offset  : Nat
  pattern  : List KLR.Core.APPair
  deriving BEq

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
  deriving BEq, Inhabited, Repr, Nonempty, FromCBOR, ToCBOR, FromJson, ToJson, FromSexp, ToSexp

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
  deriving BEq

/- Control how data is accumulated at destination locations -/
@[serde tag = 136]
inductive AccumCmd where
  | Idle
  | Zero
  | Accumulate
  | ZeroAccumulate
  | LoadAccumulate
  deriving BEq

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
  deriving BEq

/- The comparator for an affine select -/
@[serde tag = 138]
inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq
  deriving BEq

/- RMW ops for DMA -/
@[serde tag = 139]
inductive DgeComputeOp where
  | none
  | add
  deriving BEq

/- The DMA bounds check flag can either be an immediate or in a register -/
@[serde tag = 140]
inductive DmaBounds where
  | disable
  | enable
  | reg (reg : Reg)
  deriving BEq

/- Indicates whether this is the first, middle, or last matmul
instruction in a series of instructions that are accumulating into a region
of psum -/
@[serde tag = 141]
inductive MatmulGroupElement where
  | first
  | middle
  | last
  | whole
  deriving BEq

/- Whether an immediate should be written, or nothing should be written, when an index misses -/
@[serde tag = 142]
inductive IndexMissBehavior where
  | imm (value : Immediate)
  | skip
  deriving BEq

/- Which of the ops to TensorScalar should be reversed (only matters for
non-commutative operators)-/
@[serde tag = 143]
inductive TensorScalarReverseOps where
  | none
  | first
  | second
  | both
  deriving BEq

/- A representation of a contiguous set of axes of a tensor -/
@[serde tag = 144]
inductive TensorSubDim where
  | X
  | XY
  | XYZ
  | XYZW
  deriving BEq

def TensorSubDim.IsCopySubDim : TensorSubDim → Prop
| X => True | _ => False

/- Dropout instruction -/
@[serde tag = 145]
structure Dropout (Tensor : Type) (Scalar : Type) where
  dst           : Tensor
  src           : Tensor
  thresholdType : DropoutThresholdType
  threshold     : Immediate
  deriving BEq

/- Activate instruction

Performs the operation
`OUT accum= activate_func( (IN * scale_value) + bias, imm )`
-/
@[serde tag = 146]
structure Activate (Tensor : Type) (Scalar : Type) where
  dst             : Tensor
  src             : Tensor
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Immediate
  bias            : Immediate
  imm             : Immediate
  deriving BEq

/- AffineSelect instruction

Generates values using the `maskPattern` and runs them through `op`. If
the comparison is true, the value from `in` is used, otherwise `fill_value` is used.
out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
-/
@[serde tag = 147]
structure AffineSelect (Tensor : Type) (Scalar : Type) where
  dst         : Tensor
  src         : Tensor
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern
  deriving BEq

/- DmaCopy instruction

Generate descriptors to use the DMA to perform a copy. This is only used
for sbuf/psum transfers. For interacting with the HBM, use DmaHbmLoad/Store

TODO: this operation is stateful since it uses the DMA queues. How
do we represent that at the KLR level?
-/
@[serde tag = 148]
structure DmaCopy (Tensor : Type) (Scalar : Type) where
  dst            : Tensor
  src            : Tensor
  compute_op     : DgeComputeOp
  dstBoundsCheck : DmaBounds
  srcBoundsCheck : DmaBounds
  deriving BEq

/- DmaTranspose instruction
Use the DMA to reverse the dimensions of a tensor.
-/
@[serde tag = 149]
structure DmaTranspose (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- Transpose Instruction

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.
-/
@[serde tag = 150]
structure Transpose (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- LoadMaskRegister instruction

Sets a register to be the MaskRegister in the DVE
-/
@[serde tag = 151]
structure LoadMaskRegister (Tensor : Type) (Scalar : Type) where
  regNum : Reg
  deriving BEq

/-
Use the DVE to shuffle the data in src into dst based on MaskRegister
-/
@[serde tag = 152]
structure Shuffle (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- MemSet instruction

Sets `count` elements of `dst` to `value`
-/
@[serde tag = 153]
structure MemSet (Tensor : Type) (Scalar : Type) where
  dst   : Tensor
  value : Immediate
  count : Nat
  deriving BEq

/- Iota Instruction
Generates values using `pattern` and writes them to `dst` -/
@[serde tag = 154]
structure Iota (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  pattern : DataPattern
  deriving BEq

/- LoadStationary Instruction

Loads a matrix into the PE.
-/
@[serde tag = 155]
structure LoadStationary (Tensor : Type) (Scalar : Type) where
  src         : Tensor
  isTranspose : Bool
  deriving BEq

/- MatMul instruction

Performs a matmul against the currently loaded tensor using the PE -/
@[serde tag = 156]
structure MatMul (Tensor : Type) (Scalar : Type) where
  dst                : Tensor
  moving             : Tensor
  psumAccumulateFlag : MatmulGroupElement
  deriving BEq

/- LocalGather instruction
-/
@[serde tag = 157]
structure LocalGather (Tensor : Type) (Scalar : Type) where
  dst               : Tensor
  src               : Tensor
  indexMissBehavior : IndexMissBehavior
  /- Set to true when this is the last local gather operation in a group
  to free the pool buffer -/
  freePoolBuffer    : Bool
  deriving BEq

/- RangeSelect instruction
-/
@[serde tag = 158]
structure RangeSelect (Tensor : Type) (Scalar : Type) where
  dst            : Tensor
  src            : Tensor
  reduceCommand  : AccumCmd
  reduceOp       : AluOp
  base           : Float32
  fillValue      : Float32
  compOp0        : AluOp
  compOp1        : AluOp
  bound0         : Immediate
  bound1         : Immediate
  deriving BEq

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
structure ScalarTensorTensor (Tensor : Type) (Scalar : Type) where
  dst             : Tensor
  src0            : Tensor
  src1            : Tensor
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd
  deriving BEq

/- CopyPredicated instruction

Copies each element from src to dst for which predicate is not 0 -/
@[serde tag = 160]
structure CopyPredicated (Tensor : Type) (Scalar : Type) where
  dst       : Tensor
  src       : Tensor
  predicate : Tensor
  deriving BEq

/- TensorTensorScan instruction

for lane_id in range(num_active_channels):
    internal_state = imm0
    for src0_elem, src1_elem in packed(src0_mem_pattern, src1_mem_pattern):
        new_result = (src0_elem op0 internal_state) op1 src1_elem
        internal_state = new_result
        dst_mem_pattern.append(new_result)
-/
@[serde tag = 161]
structure TensorTensorScan (Tensor : Type) (Scalar : Type) where
  dst             : Tensor
  src0            : Tensor
  src1            : Tensor
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd
  deriving BEq

/- MatchValueLoad instruction

Loads values into the DVE's MatchValue registers -/
@[serde tag = 162]
structure MatchValueLoad (Tensor : Type) (Scalar : Type) where
  src : Tensor
  deriving BEq


/- FindIndex8 instruction

For each element in MatchValue register, find the first element of src that
matches and stores its index in dst. -/
@[serde tag = 163]
structure FindIndex8 (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- MatchReplace8 instruction

Same as FindIndex8, but replaces the found values in src with `replaceValue`-/
@[serde tag = 164]
structure MatchReplace8 (Tensor : Type) (Scalar : Type) where
  dst          : Tensor
  src          : Tensor
  replaceValue : Immediate
  deriving BEq

/- Max8 instruction

Finds the 8 largest values in src and writes them to dst -/
@[serde tag = 165]
structure Max8 (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- BatchNormAggregate instruction
-/
@[serde tag = 166]
structure BatchNormAggregate (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- BatchNormStats instruction
-/
@[serde tag = 167]
structure BatchNormStats (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

/- Reciprocal instruction
-/
@[serde tag = 168]
structure Reciprocal (Tensor : Type) (Scalar : Type) where
  dst  : Tensor
  src  : Tensor
  deriving BEq

/- Copy instruction
Copy src to dst -/
@[serde tag = 169]
structure Copy (Tensor : Type) (Scalar : Type) where
  dst   : Tensor
  src   : Tensor
  /- TODO: what is this for? -/
  opDim : Option TensorSubDim
  deriving BEq

/- TensorReduce instruction

Reduces a tensor along specified dimensions -/
@[serde tag = 170]
structure TensorReduce (Tensor : Type) (Scalar : Type) where
  dst          : Tensor
  src          : Tensor
  op           : AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool
  deriving BEq

/- TensorScalar instruction

output[k] = (input[k] <op0> imm0) <op1> imm1
-/
@[serde tag = 171]
structure TensorScalar (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  imm0 : Immediate
  op0 : AluOp
  imm1 : Immediate
  op1 : AluOp
  reverse : TensorScalarReverseOps
  deriving BEq

/- TensorTensor instruction
-/
@[serde tag = 172]
structure TensorTensor (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src0 : Tensor
  src1 : Tensor
  op : AluOp
  deriving BEq

@[serde tag = 1000]
structure Identity (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq

@[serde tag = 1001]
structure MakeVector (Tensor : Type) (Scalar : Type) where
  dst : VectorVar
  src : Tensor
deriving BEq

@[serde tag = 173]
inductive Operator (Tensor : Type) (Scalar : Type) where
  | activate (op : Activate Tensor Scalar)
  | affineSelect (op : AffineSelect Tensor Scalar)
  | batchNormAggregate (op : BatchNormAggregate Tensor Scalar)
  | batchNormStats (op : BatchNormStats Tensor Scalar)
  | copy (op : Copy Tensor Scalar)
  | copyPredicated (op : CopyPredicated Tensor Scalar)
  | dmaCopy (op : DmaCopy Tensor Scalar)
  | dmaTranspose (op : DmaTranspose Tensor Scalar)
  | dropout (op : Dropout Tensor Scalar)
  | findIndex8 (op : FindIndex8 Tensor Scalar)
  | iota (op : Iota Tensor Scalar)
  | loadMaskRegister (op : LoadMaskRegister Tensor Scalar)
  | loadStationary (op : LoadStationary Tensor Scalar)
  | localGather (op : LocalGather Tensor Scalar)
  | matMul (op : MatMul Tensor Scalar)
  | matchReplace8 (op : MatchReplace8 Tensor Scalar)
  | matchValueLoad (op : MatchValueLoad Tensor Scalar)
  | max8 (op : Max8 Tensor Scalar)
  | memSet (op : MemSet Tensor Scalar)
  | rangeSelect (op : RangeSelect Tensor Scalar)
  | reciprocal (op : Reciprocal Tensor Scalar)
  | scalarTensorTensor (op : ScalarTensorTensor Tensor Scalar)
  | shuffle (op : Shuffle Tensor Scalar)
  | tensorReduce (op : TensorReduce Tensor Scalar)
  | tensorScalar (op : TensorScalar Tensor Scalar)
  | tensorTensor (op : TensorTensor Tensor Scalar)
  | tensorTensorScan (op : TensorTensorScan Tensor Scalar)
  | transpose (op : Transpose Tensor Scalar)
  | matmul (dst a b : Tensor)
  | identity (op : Identity Tensor Scalar)
  | makeVector (op : MakeVector Tensor Scalar)
  deriving BEq
