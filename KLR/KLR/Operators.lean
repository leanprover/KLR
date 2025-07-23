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

import KLR.KLR.Basic

namespace KLR.KLR

/-
ALU operations supported by the HW
-/

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

/- Whether the dropout rate is how many values should be dropped or how many
values should be kept -/
inductive DropoutThresholdType
  | DropRate
  | KeepRate

/- Control how data is accumulated at destination locations -/
inductive AccumCmd where
  | Idle
  | Zero
  | Accumulate
  | ZeroAccumulate
  | LoadAccumulate

/- TODO: we need a way to represent activation function tables -/
inductive ActivationFunc

/- The comparator for an affine select -/
inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq

/- Whether DMA operations should be bounds checked -/
inductive DmaBoundCheck where
  | disable
  | enable

/- RMW ops for DMA -/
inductive DgeComputeOp
  | NONE
  | ADD

/- The DMA bounds check flag can either be an immediate or in a register -/
inductive DmaBounds
  | check (_  : DmaBoundCheck)
  | reg (_  : Reg)

/- Indicates whether this is the first, middle, or last matmul
instruction in a series of instructions that are accumulating into a region
of psum -/
inductive MatmulGroupElement where
  | first
  | middle
  | last

/- Whether an immediate should be written, or nothing should be written, when an index misses -/
inductive IndexMissBehavior where
| ImmediateWrite (value : Immediate)
| SkipWrite

/- Which of the ops to TensorScalar should be reversed (only matters for
non-commutative operators)-/
inductive TensorScalarReverseOps where
| None
| First
| Second
| Both

/- A representation of a contiguous set of axes of a tensor -/
inductive TensorSubDim where
| X
| XY
| XYZ
| XYZW

def TensorSubDim.IsCopySubDim  : TensorSubDim → Prop
| X => True | _ => False

inductive ArithNegated  : AluOp → Type _

def AluOp.IsArith  : AluOp → Prop
| .abs | .add | .average | .bypass | .divide | .is_equal | .is_ge | .is_gt | .is_le | .is_lt | .max | .min | .mod | .mult | .not_equal | .pow | .rsqrt | .subtract => True
| _ => False

/-- The ALUOps for a TensorReduceArithOp -/
def AluOp.IsTensorReduceArithOp  : AluOp → Prop
| abs | add | average | bypass | is_equal | is_ge | is_gt | is_le | is_lt | max | min | mult | not_equal | subtract => True
| _ => False

/-- The ALUOps for a TensorReduceBitvecOp -/
def AluOp.IsTensorReduceBitwiseOp  : AluOp → Prop
| arith_shift_left | arith_shift_right | bitwise_and | bitwise_or | bitwise_xor | logical_and | logical_or | logical_shift_left | logical_shift_right | logical_xor => True
| _ => False

/- ActivationFunctionLoad -/
structure ActivationTableLoad where
  ActTableSelect : UInt8

/- Dropout instruction -/
structure Dropout where
  dst           : TensorRef
  src           : TensorRef
  thresholdType : DropoutThresholdType
  threshold     : Immediate

/- Activate instruction

Performs the operation
`OUT accum= activate_func( (IN * scale_value)] + bias, imm )`
-/
structure Activate where
  dst             : TensorRef
  src             : TensorRef
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Immediate
  bias            : Immediate
  imm             : Immediate

/- AffineSelect instruction

Generates values using the `maskPattern` and runs them through `op`. If
the comparison is true, the value from `in` is used, otherwise `fill_value` is used.
out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
-/
structure AffineSelect where
  dst         : TensorRef
  src         : TensorRef
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern

/- DmaCopy instruction

Generate descriptors to use the DMA to perform a copy.

TODO: this operation is stateful since it uses the DMA queues. How
do we represent that at the KLR level?
-/
structure DmaCopy where
  dst            : TensorRef
  src            : TensorRef
  compute_op     : DgeComputeOp
  dstBoundsCheck : DmaBounds
  srcBoundsCheck : DmaBounds

/- DmaTranspose instruction
Use the DMA to reverse the dimensions of a tensor.
-/
structure DmaTranspose where
  dst : TensorRef
  src : TensorRef

/- Transpose Instructino

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.
-/
structure Transpose where
  dst : TensorRef
  src : TensorRef

/- LoadMaskRegister instruction

Sets a register to be the MaskRegister in the DVE
-/
structure LoadMaskRegister where
  regNum : Reg

/-
Use the DVE to shuffle the data in src into dst based on MaskRegister
-/
structure Shuffle where
  dst : TensorRef
  src : TensorRef

/- MemSet instruction

Sets `count` elements of `dst` to `value`
-/
structure MemSet where
  dst   : TensorRef
  value : UInt32
  count : Nat

/- Iota Instruction
Generates values using `pattern` and writes them to `dst` -/
structure Iota where
  dst : TensorRef
  pattern : DataPattern

/- LoadStationary Instruction

Loads a matrix into the PE.
-/
structure LoadStationary where
  src         : TensorRef
  isTranspose : Bool

/- MatMul instruction

Performs a matmul against the currently loaded tensor using the PE -/
structure MatMul where
  dst                : TensorRef
  moving             : TensorRef
  psumAccumulateFlag : MatmulGroupElement

/- LocalGather instruction
-/
structure LocalGather where
  dst               : TensorRef
  src               : TensorRef
  indexMissBehavior : IndexMissBehavior
  /- Set to true when this is the last local gather operation in a group
  to free the pool buffer -/
  freePoolBuffer    : Bool

/- RangeSelect instruction
-/
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
structure ScalarTensorTensor where
  dst             : TensorRef
  src0            : TensorRef
  src1            : TensorRef
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd

/- CopyPredicated instruction

Copies each element from src to dst for which predicate is not 0 -/
structure CopyPredicated where
  dst       : TensorRef
  src       : TensorRef
  predicate : TensorRef

/- TensorTensorScan instruction

for lane_id in range(num_active_channels):
    internal_state = imm0
    for src0_elem, src1_elem in packed(src0_mem_pattern, src1_mem_pattern):
        new_result = (src0_elem op0 internal_state) op1 src1_elem
        internal_state = new_result
        dst_mem_pattern.append(new_result)
-/
structure TensorTensorScan where
  dst             : TensorRef
  src0            : TensorRef
  src1            : TensorRef
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd

/- MatchValueLoad instruction

Loads values into the DVE's MatchValue registers -/
structure MatchValueLoad where
  src : TensorRef


/- FindIndex8 instruction

For each element in MatchValue register, find the first element of src that
matches and stores its index in dst. -/
structure FindIndex8 where
  dst : TensorRef
  src : TensorRef

/- MatchReplace8 instruction

Same as FindIndex8, but replaces the found values in src with `replaceValue`-/
structure MatchReplace8 where
  dst          : TensorRef
  src          : TensorRef
  replaceValue : Float32

/- Max8 instruction

Finds the 8 largest values in src and writes them to dst -/
structure Max8 where
  dst : TensorRef
  src : TensorRef

-- TODO : @govereau do we need to support these custom ops if they're Sunda-specific?
/-
inductive SundaAddr
inductive CustomOpArgLocation where
| Invalid
| Sbuf
| Hbm
abbrev TPBAddr  := UInt32
inductive CustomOpTensorShape where
| InlineShape8d (data : List UInt16) -- there are 8 of these
| OutOfLineShape (addr : TPBAddr)
| InlineShape4d (data : List UInt32) -- there are 4 of these
inductive CustomOpTensorStorage where
| tpb (addr : TPBAddr) (num_elem : UInt32) (num_partitions : UInt8) (num_elemens_per_block : UInt32)
| hbm (addr : SundaAddr) (num_elem : UInt32)
structure CustomOpArgTensor where
  location        : CustomOpArgLocation
  framework_shape : CustomOpTensorShape
  storage         : CustomOpTensorStorage
structure CustomOpArgArrayOfTensor where
  num_object : UInt32
inductive CustomOpArgType where
| Invalid
| Tensor
| ArrayOfTensor
inductive CustomOpArgUnion where
| tensor (t : CustomOpArgTensor)
| array_of_tensor (ar : CustomOpArgArrayOfTensor)
structure CustomOpPayload where
  arg : CustomOpArgUnion
-/

/- BatchNormAggregate instruction
-/
structure BatchNormAggregate where
  dst : TensorRef
  src : TensorRef

/- BatchNormStats instruction
-/
structure BatchNormStats where
  dst : TensorRef
  src : TensorRef

/- Reciprocal instruction
-/
structure Reciprocal where
  dst  : TensorRef
  src  : TensorRef

/- Copy instruction
Copy src to dst -/
structure Copy where
  dst   : TensorRef
  src   : TensorRef
  /- TODO: what is this for? -/
  opDim : Option TensorSubDim

/- TensorReduce instruction

Reduces a tensor along specified dimensions -/
structure TensorReduce where
  dst          : TensorRef
  src          : TensorRef
  op           : AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool

inductive Operator where
  | Activate (op : Activate)
  | AffineSelect (op : AffineSelect)
  | BatchNormAggregate (op : BatchNormAggregate)
  | BatchNormStats (op : BatchNormStats)
  | Copy (op : Copy)
  | CopyPredicated (op : CopyPredicated)
  | DmaCopy (op : DmaCopy)
  | DmaTranspose (op : DmaTranspose)
  | Dropout (op : Dropout)
  | FindIndex8 (op : FindIndex8)
  | Iota (op : Iota)
  | LoadMaskRegister (op : LoadMaskRegister)
  | LoadStationary (op : LoadStationary)
  | LocalGather (op : LocalGather)
  | MatMul (op : MatMul)
  | MatchReplace8 (op : MatchReplace8)
  | MatchValueLoad (op : MatchValueLoad)
  | Max8 (op : Max8)
  | MemSet (op : MemSet)
  | RangeSelect (op : RangeSelect)
  | Reciprocal (op : Reciprocal)
  | ScalarTensorTensor (op : ScalarTensorTensor)
  | Shuffle (op : Shuffle)
  | TensorReduce (op : TensorReduce)
  | TensorTensorScan (op : TensorTensorScan)
  | Transpose (op : Transpose)
