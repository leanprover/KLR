/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import KLR.KLR.Basic

namespace KLR.KLR

inductive Reg where
| reg (r : Nat) -- register number

inductive Immediate where
| register -- : TODO
| pointer -- : TODO
| int (i : Int32)
| float (f : Float32)
deriving BEq, Repr

inductive ActivationImm where
| register -- : TODO
| pointer -- : TODO
| float (f : Float32)
deriving BEq, Repr

inductive DropoutThresholdType
| DropRate
| KeepRate

structure Dropout where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d
    threshold_type:        DropoutThresholdType
    threshold:             Immediate

inductive AccumCmd where
| Idle
| Zero
| Accumulate
| ZeroAccumulate
| LoadAccumulate

structure Activate where
    accumulator_cmd:       AccumCmd
    src_mem_pattern:       InputTensor3d
    in_bias_dtype:         (Dtype × Dtype)
    activation_func:       u8
    scale_value:           Immediate
    bias:                  Immediate
    imm:                   Immediate
    dst_mem_pattern:       OutputTensor3d

inductive ActivationFunc where
| unknown -- TODO: what activation funcs are valid?

-- s3_d3_ac.rs
-- performs the operation `OUT accum= activate_func( (IN * scale_value)] + bias, imm )`
structure Activate2 where
  dst:                   OutputTensor3d
  src:                   InputTensor3d
  accumulator_cmd:       AccumCmd
  activation_func:       ActivationFunc
  scale:                 Immediate
  bias:                  Immediate
  imm:                   Immediate

inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq

/-
Used for Iota and AffineSelect, represents something similar to an
access pattern but that is only used to generate data, not to index
-/
structure DataPattern where
  offset : Nat
  pattern : List APPair

-- s2d2_ts_as.rs
-- out[k] = (mask[k] <op> 0) ? in[k] : fill_value
structure AffineSelect where
    dst:       OutputTensor3d
    src:       InputTensor3d
    fill_mode:             AffineSelectCmp
    fill_reg:              Reg -- must be a float value
    mask_pattern:          DataPattern

inductive DmaBoundCheck where
  | disable
  | enable

-- RMW Ops for DMA
inductive DgeComputeOp
  | NONE
  | ADD
  | MULTIPLY
  | MAX
  | MIN

-- Paul look at this pls
inductive DMABounds
| check (_ : DmaBoundCheck)
| reg (_ : Reg)

-- dma_direct2d.rs
/-
TODO: there are constraints around how many dimensions you can use
and whether theyre stored in immediates or registers, but at the KLR
level it's probably easiest to just have a simple model of DMA copies
and we can figure out how to turn them into ISA instructions when
compiling out of KLR.
-/
structure DmaCopy where
  dst:                   OutputTensor3d
  src:                   InputTensor3d
  compute_op:            DgeComputeOp
  dst_bounds_checked:  DMABounds
  src_bounds_checked:  DMABounds


/-
dma_direct2d_expose.rs

Perform arbitrary dimension (up to 4d) DMA transposes from hbm/sbuf to sbuf.
Here, transpose means "reverse the order of the dimensions".

TODO: this may be more complicated than described above
-/
structure DmaTranspose where
  dst:                  OutputTensor3d
  src:                  InputTensor3d

/-
s4d4_tr.rs or s3d3_mm.rs

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.

OR use the PE engine to do a transpose on 2d tensors, where the normal PE engine restrictions apply.
-/
structure Transpose where
  dst:                  OutputTensor3d
  src:                  InputTensor3d

/-
s4d4_tr.rs or s3d3_mm.rs

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.

OR use the PE engine to do a transpose on 2d tensors, where the normal PE engine restrictions apply.
-/
structure Shuffle where
  dst:                  OutputTensor3d
  src:                  InputTensor3d
  shuffle_pattern:      List Nat -- TODO: this is exactly 32 elements


/-
d4_mr.md
-/
structure MemSet where
    dst:    OutputTensor3d
    value : UInt32
    count:     Nat

/-
d4_iota.rs
-/
structure Iota where
  dst: OutputTensor3d
  src: DataPattern

/-
Indicates whether this is the first, middle, or last matmul
instruction that is accumulating into a region of psum
-/
inductive MatmulGroupElement where
  | first
  | middle
  | last

/-
s3d3_mm.rs

This gets turned into a load stationary and then a matmul instruction.
-/
structure MatMul where
    dst:                   OutputTensor3d
    stationary:            InputTensor3d
    moving:                InputTensor3d
    psum_accumulate_flags: MatmulGroupElement

inductive IndexMissBehavior where
| ImmediateWrite
| SkipWrite

structure LocalGather where
    src_mem_pattern:       InputTensor3d
    index_miss_behavior:   IndexMissBehavior
    free_pool_buffer: UInt8
    immediate:             Immediate
    dst_mem_pattern:       OutputTensor3d


structure RangeSelect where
    reduce_cmd:            AccumCmd
    reduce_op:             AluOp
    base:                  f32
    fill_val:              f32
    src_mem_pattern:       InputTensor3d
    comp_op0:              AluOp
    comp_op1:              AluOp
    bound0:                Immediate
    bound1:                Immediate
    dst_mem_pattern:       OutputTensor3d

inductive TensScalarRevOps
| None
| First
| Second
| Both

structure ScalarTensorTensor where
    src0_mem_pattern:      InputTensor3d
    src1_mem_pattern:      InputTensor3d
    op0:                   AluOp
    op1:                   AluOp
    reverse_operands:      TensScalarRevOps
    imm0_src:              Immediate
    accumulator_cmd:       AccumCmd
    dst_mem_pattern:       OutputTensor3d

structure CopyPredicated where
    op:                    AluOp
    src0_mem_pattern:      InputTensor3d
    src1_mem_pattern:      InputTensor3d
    dst_mem_pattern:       OutputTensor3d

structure TensorTensorScan where
    src0_mem_pattern:      InputTensor3d
    src1_mem_pattern:      InputTensor3d
    op0:                   AluOp
    op1:                   AluOp
    reverse_operands:      TensScalarRevOps
    imm0_src:              Immediate
    accumulator_cmd:       AccumCmd
    dst_mem_pattern:       OutputTensor3d

structure FindIndex8 where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d

structure MatchReplace8 where
    src_mem_pattern:       InputTensor3d
    immediate:             Float32
    dst_mem_pattern:       OutputTensor3d

structure Max8 where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d


inductive CustomOpArgLocation where
| Invalid
| Sbuf
| Hbm

abbrev TPBAddr := UInt32

inductive CustomOpTensorShape where
| InlineShape8d (data: List UInt16) -- there are 8 of these
| OutOfLineShape (addr: TPBAddr)
| InlineShape4d (data: List UInt32) -- there are 4 of these

inductive CustomOpTensorStorage where
| tpb (addr: TPBAddr) (num_elem: UInt32) (num_partitions: UInt8) (num_elemens_per_block: UInt32)
| hbm (addr: SundaAddr) (num_elem: UInt32)

structure CustomOpArgTensor where
  location: CustomOpArgLocation
  framework_shape: CustomOpTensorShape
  storage : CustomOpTensorStorage

structure CustomOpArgArrayOfTensor where
  num_object : UInt32

inductive CustomOpArgType where
| Invalid
| Tensor
| ArrayOfTensor

inductive CustomOpArgUnion where
| tensor (t: CustomOpArgTensor)
| array_of_tensor (ar: CustomOpArgArrayOfTensor)

structure CustomOpPayload where
    arg:                            CustomOpArgUnion

structure BatchNormAggregate where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d

structure BatchNormStats where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d


-- TODO: Not sure about these next two, To support dynamic copy
-- it needs to replicate the dynamic behaviors in Addr4.

structure OutputTensor4d where -- TODO
  freePattern: List APPair
  offset : Nat := 0
  dtype : Dtype

structure InputTensor4d extends OutputTensor4d where
  parNum : Nat

-- Not sure if negated field is allowed or not
structure Reciprocal where
  src : InputTensor4d
  dst : OutputTensor4d
  dtype : Dtype

inductive TensorSubDim where
| Unused
| X
| XY
| XYZ
| XYZW

def TensorSubDim.IsCopySubDim : TensorSubDim → Prop
| Unused | X => True | _ => False

structure Copy where
  dst:                   OutputTensor4d
  src:                   InputTensor4d
  dtype : Dtype
  op_dim : TensorSubDim
  copy_dim : op_dim.IsCopySubDim

inductive ArithNegated : AluOp → Type _

def AluOp.IsArith : AluOp → Prop
| .abs | .add | .average | .bypass | .divide | .is_equal | .is_ge | .is_gt | .is_le | .is_lt | .max | .min | .mod | .mult | .not_equal | .pow | .rsqrt | .subtract => True
| _ => False

/-- The ALUOps for a TensorReduceArithOp -/
def AluOp.IsTensorReduceArithOp : AluOp → Prop
| abs | add | average | bypass | is_equal | is_ge | is_gt | is_le | is_lt | max | min | mult | not_equal | subtract => True
| _ => False

/-- The ALUOps for a TensorReduceBitvecOp -/
def AluOp.IsTensorReduceBitwiseOp : AluOp → Prop
| arith_shift_left | arith_shift_right | bitwise_and | bitwise_or | bitwise_xor | logical_and | logical_or | logical_shift_left | logical_shift_right | logical_xor => True
| _ => False

/-- Negated flag is ignored for non-arithmetic operations. -/
structure TensorReduce where
  src         : InputTensor4d
  src_dtype   : Dtype
  dst_dtype   : Dtype
  op          : AluOp
  op_dim      : TensorSubDim
  negated     : op.IsTensorReduceArithOp → Bool
  dst         : OutputTensor4d

inductive Operator where
  -- TODO
  deriving Repr, BEq
