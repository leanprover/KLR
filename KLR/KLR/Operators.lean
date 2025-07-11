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

structure Dropout where
  dst           : TensorView
  src           : TensorView
  thresholdType : DropoutThresholdType
  threshold     : Immediate

inductive AccumCmd where
  | Idle
  | Zero
  | Accumulate
  | ZeroAccumulate
  | LoadAccumulate

inductive ActivationFunc where
  | unknown -- TODO : what activation funcs are valid?

-- performs the operation `OUT accum= activate_func( (IN * scale_value)] + bias, imm )`
structure Activate where
  dst             : TensorView
  src             : TensorView
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Immediate
  bias            : Immediate
  imm             : Immediate

inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq

-- out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
structure AffineSelect where
  dst         : TensorView
  src         : TensorView
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern

inductive DmaBoundCheck where
  | disable
  | enable

-- RMW Ops for DMA
inductive DgeComputeOp
  | NONE
  | ADD

inductive DMABounds
  | check (_  : DmaBoundCheck)
  | reg (_  : Reg)

/-
TODO : there are constraints around how many dimensions you can use
and whether theyre stored in immediates or registers, but at the KLR
level it's probably easiest to just have a simple model of DMA copies
and we can figure out how to turn them into ISA instructions when
compiling out of KLR.
-/
structure DmaCopy where
  dst            : TensorView
  src            : TensorView
  compute_op     : DgeComputeOp
  dstBoundsCheck : DMABounds
  srcBoundsCheck : DMABounds

/-
Perform arbitrary dimension (up to 4d) DMA transposes from hbm/sbuf to sbuf.
Here, transpose means "reverse the order of the dimensions".

TODO : this may be more complicated than described above
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


-- TODO : This instruction only needs to exist if the `shuffle_pattern` variant below
-- is absent. @govereau what to do about this
structure LoadMaskRegister where
  regNum : Reg
/-
Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.

OR use the PE engine to do a transpose on 2d tensors, where the normal PE engine restrictions apply.
-/
structure Shuffle where
  dst : TensorView
  src : TensorView
  --shuffle_pattern : Reg

structure MemSet where
  dst   : TensorView
  value : UInt32
  count : Nat

structure Iota where
  dst : TensorView
  src : DataPattern

/-
Indicates whether this is the first, middle, or last matmul
instruction that is accumulating into a region of psum
-/
inductive MatmulGroupElement where
  | first
  | middle
  | last

/- Loads a matrix into the PE -/
structure LoadStationary where
  src         : TensorView
  isTranspose : Bool

structure MatMul where
  dst                : TensorView
  moving             : TensorView
  psumAccumulateFlag : MatmulGroupElement

inductive IndexMissBehavior where
| ImmediateWrite (value : Immediate)
| SkipWrite

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

inductive TensorScalarReverseOps where
| None
| First
| Second
| Both

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

-- Not sure if negated field is allowed or not
structure Reciprocal where
  dst  : TensorView
  src  : TensorView

inductive TensorSubDim where
| Unused
| X
| XY
| XYZ
| XYZW

def TensorSubDim.IsCopySubDim  : TensorSubDim → Prop
| Unused | X => True | _ => False

structure Copy where
  dst   : TensorView
  src   : TensorView
  opDim : TensorSubDim
  --copy_dim  : op_dim.IsCopySubDim

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

structure TensorReduce where
  dst          : TensorView
  src          : TensorView
  op           : AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool

inductive Operator
-- todo : add a variant for each op struct
