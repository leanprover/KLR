/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import KLR.KLR.Basic

namespace KLR.KLR

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

inductive DmaBoundCheck where
  | disable
  | enable

-- RMW Ops for DMA
inductive DgeComputeOp
  | NONE
  | ADD

/- The DMA bounds value can either be an immediate or in a register -/
inductive DmaBounds
  | check (_  : DmaBoundCheck)
  | reg (_  : Reg)

/-
Indicates whether this is the first, middle, or last matmul
instruction that is accumulating into a region of psum
-/
inductive MatmulGroupElement where
  | first
  | middle
  | last

/- Whether an immediate should be written, or nothing should be written, when an index misses -/
inductive IndexMissBehavior where
| ImmediateWrite (value : Immediate)
| SkipWrite

/- Which of the ops to TensorScalar should be reversed -/
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


structure Dropout where
  dst           : TensorView
  src           : TensorView
  thresholdType : DropoutThresholdType
  threshold     : Immediate

/- performs the operation
`OUT accum= activate_func( (IN * scale_value)] + bias, imm )`
-/
structure Activate where
  dst             : TensorView
  src             : TensorView
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Immediate
  bias            : Immediate
  imm             : Immediate

/- Generates values using the `maskPattern` and runs them through `op`. If
the comparison is true, the value from `in` is used, otherwise `fill_value` is used.

out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
-/
structure AffineSelect where
  dst         : TensorView
  src         : TensorView
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern

/-
Use the DMA to perform a copy.

TODO: this operation is stateful since it uses the DMA queues. How
do we represent that at the KLR level?
-/
structure DmaCopy where
  dst            : TensorView
  src            : TensorView
  compute_op     : DgeComputeOp
  dstBoundsCheck : DMABounds
  srcBoundsCheck : DMABounds

/-
Use the DMA to reverse the dimensions of a tensor.
-/
structure DmaTranspose where
  dst : TensorView
  src : TensorView

/-
Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.

OR use the PE engine to do a transpose on 2d tensors, where the normal PE engine restrictions apply.
-/
structure Transpose where
  dst : TensorView
  src : TensorView
  engine : Engine

/-
Loads a register into the MaskRegister

TODO : This instruction only needs to exist if the `shuffle_pattern` variant below
is absent. @govereau what to do about this-/
structure LoadMaskRegister where
  regNum : Reg

/-
Use the DVE to shuffle the data in src into dst based on MaskRegister
-/
structure Shuffle where
  dst : TensorView
  src : TensorView
  --shuffle_pattern : Reg

/- Sets `count` elements of `dst` to `value` -/
structure MemSet where
  dst   : TensorView
  value : UInt32
  count : Nat

/- Generates values using `src` and writes them to `dst` -/
structure Iota where
  dst : TensorView
  src : DataPattern

/- Loads a matrix into the PE -/
structure LoadStationary where
  src         : TensorView
  isTranspose : Bool

/- Performs a matmul using the PE -/
structure MatMul where
  dst                : TensorView
  moving             : TensorView
  psumAccumulateFlag : MatmulGroupElement

structure LocalGather where
  dst               : TensorView
  src               : TensorView
  indexMissBehavior : IndexMissBehavior
  /- Set to true when this is the last local gather operation in a group
  to free the pool buffer -/
  freePoolBuffer    : Bool

structure RangeSelect where
  dst            : TensorView
  src            : TensorView
  reduceCommand  : AccumCmd
  reduceOp       : AluOp
  base           : Float32
  fillValue      : Float32
  compOp0        : AluOp
  compOp1        : AluOp
  bound0         : Immediate
  bound1         : Immediate

/-
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
  dst             : TensorView
  src0            : TensorView
  src1            : TensorView
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd

/- Copies each element from src to dst for which predicate is not 0 -/
structure CopyPredicated where
  dst       : TensorView
  src       : TensorView
  predicate : TensorView

/-
for lane_id in range(num_active_channels):
    internal_state = imm0
    for src0_elem, src1_elem in packed(src0_mem_pattern, src1_mem_pattern):
        new_result = (src0_elem op0 internal_state) op1 src1_elem
        internal_state = new_result
        dst_mem_pattern.append(new_result)
-/
structure TensorTensorScan where
  dst             : TensorView
  src0            : TensorView
  src1            : TensorView
  op0             : AluOp
  op1             : AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Immediate
  accumulatorCmd  : AccumCmd

/- Loads values into the DVE's MatchValue registers -/
structure MatchValueLoad where
  src : TensorView

/- For each element in MatchValue register, find the first element of src that
matches and stores its index in dst. -/
structure FindIndex8 where
  dst : TensorView
  src : TensorView

/- Same as FindIndex8, but replaces the found values in src with `replaceValue`-/
structure MatchReplace8 where
  dst          : TensorView
  src          : TensorView
  replaceValue : Float32

/- Finds the 8 largest values in src and writes them to dst -/
structure Max8 where
  dst : TensorView
  src : TensorView

-- TODO : @govereau do we need to support these custom ops if they're Sunda-specific?
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

structure BatchNormAggregate where
  dst : TensorView
  src : TensorView

structure BatchNormStats where
  dst : TensorView
  src : TensorView

structure Reciprocal where
  dst  : TensorView
  src  : TensorView

/- Copy src to dst -/
structure Copy where
  dst   : TensorView
  src   : TensorView
  /- TODO: what is this for? -/
  opDim : Option TensorSubDim
  --copy_dim  : op_dim.IsCopySubDim

/- Reduces a tensor along specified dimensions -/
structure TensorReduce where
  dst          : TensorView
  src          : TensorView
  op           : AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool

inductive Operator
