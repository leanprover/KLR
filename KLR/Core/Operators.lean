/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

/-
# Definition of operators


Operators can appear in a call node, and can be thought of as functions that
take arguments and return results. However, an operator may have several
variations, and these variations show up as parameters within the operator and
not as arguments of the call node. A typical example is:

  .store t [] (.call (.operator (.tensorScalar ts)) [a,b] [])

where `ts` contains the tensor scalar parameters:

  let ts := TensorScalar { op0 := .add, ..}
  let ts := TensorScalar { op0 := .multiply, op1 := add, ..}

The choice of argument or parameter may seem arbitrary; these definitions
follow the hardware ISA as close as possible.
-/

namespace KLR.Core

-- Compute Engines
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, Repr

-- Memory types
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

/-
ALU operations supported by the HW
Only used by: TensorScalar, TensorScalarPtr, TensorReduce, TensorTensor
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

-- TODO: should these be Int32 and Float32?
-- At the python level: no, after tracing: yes.
-- Perhaps FromNKI can check for overflow and raise an error?
inductive Const where
  | int (i : Int)
  | float (f : Float)
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

-- Tensor-Scalar operator
-- Note: this is not supported in NKI, but it useful for testing.
structure TensorScalar where
  op0 : AluOp
  const0 : Float32
  reverse0 : Bool
  op1 : AluOp
  const1 : Float32
  reverse1 : Bool
  deriving Repr, BEq

-- Tensor-Scalar where the scalars are loaded from memory
structure TensorScalarAddr where
  op0 : AluOp
  reverse0 : Bool
  op1 : AluOp
  reverse1 : Bool
  deriving Repr, BEq

abbrev Opcode := UInt16

structure OutputTensor3d where -- TODO
  freePattern: List APPair
  offset : Nat := 0
  dtype : Dtype

structure InputTensor3d extends OutputTensor3d where  -- TOOD
  parNum : Nat

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


inductive IndexMissBehavior where
| ImmediateWrite
| SkipWrite

structure LocalGather where
    src_mem_pattern:       InputTensor3d
    index_miss_behavior:   IndexMissBehavior
    free_pool_buffer:      u8
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

structure MatchReplace8
    src_mem_pattern:       InputTensor3d
    immediate:             f32
    dst_mem_pattern:       OutputTensor3d

structure Max8 where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d


inductive CustomOpArgLocation where
| Invalid
| Sbuf
| Hbm

abbrev TPBAddr := Uint32

inductive CustomOpTensorShape where
| InlineShape8d (data: List UInt16) -- there are 8 of these
| OutOfLineShape (addr: TPBAddr)
| InlineShape4d (data: List UInt32) -- there are 4 of these

inductive CustomOpTensorStorage where
| tpb (addr: TPBAddr, num_elem: Uint32, num_partitions: UInt8, num_elemens_per_block: UInt32)
| hbm (addr: SundaAddr, num_elem: UInt32)

structure CustomOpArgTensor where
  location: CustomOpArgLocation
  framework_shape: CustomOpTensorShape
  storage : CustomOpTensorStorage

structure CustomOpArgArrayOfTensor where
  num_object : Uint32

inductive CustomOpArgType where
| Invalid
| Tensor
| ArrayOfTensor

inductive CustomOpargUnion where
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

structure Reciprocal where
-- pub struct s4d4_tr_struct {
--     pub header:                Header,          // 4    ( 0 -  3)
--     pub events:                Events,          // 8    ( 4 - 11)
--     pub src_mem_pattern:       MemPattern4d,    // 20   (12 - 31)
--     pub in_dtype:              Dtype,           // 1    (32     )
--     pub out_dtype:             Dtype,           // 1    (33     )
--     pub num_active_channels:   u8,              // 1    (34     )
--     pub negated:               u8,              // 1    (35     )
--     pub op:                    AluOp,           // 1    (36     )
--     pub op_dim:                TensorSubdim,    // 1    (37     )
--     pub mask_enable:           u8,              // 1    (38     )
--     pub reserved1:             [u8;5],          // 5    (39 - 43)
--     pub dst_mem_pattern:       MemPattern4d,    // 20   (44 - 63)
-- }

structure Copy where
-- pub struct s4d4_tr_struct {
--     pub header:                Header,          // 4    ( 0 -  3)
--     pub events:                Events,          // 8    ( 4 - 11)
--     pub src_mem_pattern:       MemPattern4d,    // 20   (12 - 31)
--     pub in_dtype:              Dtype,           // 1    (32     )
--     pub out_dtype:             Dtype,           // 1    (33     )
--     pub num_active_channels:   u8,              // 1    (34     )
--     pub negated:               u8,              // 1    (35     )
--     pub op:                    AluOp,           // 1    (36     )
--     pub op_dim:                TensorSubdim,    // 1    (37     )
--     pub mask_enable:           u8,              // 1    (38     )
--     pub reserved1:             [u8;5],          // 5    (39 - 43)
--     pub dst_mem_pattern:       MemPattern4d,    // 20   (44 - 63)
-- }

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

inductive TensorSubDim where
| Unused
| X
| XY
| XYZ
| XYZW

/-- Negated flag is ignored for non-arithmetic operations. -/
structure TensorReduce where
  src         : InputTensor3d
  src_dtype   : Dtype
  dst_dtype   : Dtype
  op          : AluOp
  op_dim      : TensorSubDim
  negated     : op.IsTensorReduceArithOp → Bool
  dst         : OutputTensor3d

-- All of the operators
inductive Operator where
  | load : Operator
  | save : Operator
  | memset : Nat -> Operator /- the Nat operand is uint32_t -/
  | tensorScalar : TensorScalar -> Operator
  | tensorScalarAddr : TensorScalarAddr -> Operator
  deriving Repr, BEq
