/-
The definition of the KLR AST

This is based on the nki.isa API, which can be seen at
https://github.com/aws-neuron/aws-neuron-sdk/blob/094394bc464872f3387d315ae446576583660422/general/nki/api/nki/isa/__init__.py

-/

import TensorLib.Tensor
import TensorLib.Shape
import TensorLib.Dtype
import KLR.Core

open TensorLib(Tensor Shape Dtype)
open KLR.Core(Access TensorName)

namespace KLR.KLR

inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, Repr

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

/- ALU operations supported by the HW -/
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

inductive Const where
  | int (i : Int32)
  | float (f : Float32)
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

-- TODO: This is generated from nki.isa, make sure it matches NRC
inductive DgeMode where
  | none      -- Not using DGE
  | swdge     -- Software DGE
  | hwdge     -- Hardware DGE
  | unknown   -- Unknown DGE mode, let compiler decide
deriving Repr, DecidableEq

-- TODO: This is generated from nki.isa, make sure it matches NRC
inductive OobMode where
  | error     -- Raise error on out-of-bounds
  | skip      -- Skip out-of-bounds operations
deriving Repr, DecidableEq

-- TODO: This is generated from nki.isa, make sure it matches NRC
inductive ReduceCmd where
  | idle           -- Not using accumulator registers
  | reset          -- Reset accumulator registers
  | reset_reduce   -- Reset then accumulate
  | reduce         -- Keep accumulating
deriving Repr, DecidableEq

-- TODO: This is generated from nki.isa, make sure it matches NRC
inductive ActivationFunc where
  | id
  | relu
  | sigmoid
  | tanh
  | gelu
  | exp
  | log
  | sqrt
  | rsqrt
deriving Repr, DecidableEq

-- Operand types
inductive Operand  where
  | scalar (_ : Float32)
  | vector (_ : Access)
  | tile  (_ : Access)
deriving Repr, Inhabited


/-
====================== TODO: ==========================
All the following structures are generated from nki.isa. We need to go through
and make sure they match the NRC definitions. If an NRC definition is missing,
then we need to check NeuronArchIsaSrc instead.
-/

-- Activation instruction
structure Activation  where
  dst : Access
  op : ActivationFunc
  data : Access
  bias : Option Operand
  scale : Operand
  reduce_op : Option AluOp
  reduce_res : Option Access
  reduce_cmd : ReduceCmd
  dtype : Option Dtype
deriving Repr

-- Activation with reduction
structure ActivationReduce  where
  dst : Access
  op : ActivationFunc
  data : Access
  reduce_op : AluOp
  reduce_res : Access
  bias : Option Operand
  scale : Operand
  dtype : Option Dtype
deriving Repr

-- Affine select operation
structure AffineSelect  where
  dst : Access
  pred : Access
  on_true_tile : Access
  on_false_value : Float
  dtype : Option Dtype
deriving Repr

-- Batch normalization aggregation
structure BnAggr  where
  dst : Access
  data : Access
  dtype : Option Dtype
deriving Repr

-- Batch normalization statistics
structure BnStats  where
  dst : Access
  data : Access
  dtype : Option Dtype
deriving Repr

-- DMA copy operation
structure DmaCopy  where
  dst : Access
  src : Access
  dst_rmw_op : Option AluOp
  oob_mode : OobMode
  dge_mode : DgeMode
deriving Repr

-- DMA transpose
structure DmaTranspose  where
  src : Access
  dtype : Option Dtype
deriving Repr

-- Dropout operation
structure Dropout  where
  data : Access
  prob : Operand
  dtype : Option Dtype
deriving Repr

-- Iota
structure Iota  where
  expr : Access  -- Affine expression (dtype : Dtype)
deriving Repr

-- Local gather operation
structure LocalGather  where
  src_buffer : Access
  index : Access
  num_elem_per_idx : Nat
  num_valid_indices : Option Nat
deriving Repr

-- Max8 operation
structure Max8  where
  src : Access
  dtype : Option Dtype
deriving Repr

-- Memory set operation
structure Memset  where
  shape : Shape
  value : Float
  dtype : Dtype
  engine : Engine
deriving Repr

-- Matrix multiplication
structure NcMatmul  where
  stationary : Access
  moving : Access
  is_stationary_onezero : Bool
  is_moving_onezero : Bool
  is_transpose : Bool
  tile_position : Option (Nat × Nat)
  tile_size : Option (Nat × Nat)
deriving Repr

-- Stream shuffle
structure NcStreamShuffle  where
  src : Access
  shuffle_mask : List Nat
  dtype : Option Dtype
deriving Repr

-- Transpose operation
structure NcTranspose  where
  data : Access
  dtype : Option Dtype
  engine : Engine
deriving Repr

-- Range select operation
structure RangeSelect  where
  on_true_tile : Access
  comp_op0 : AluOp
  comp_op1 : AluOp
  bound0 : Access
  bound1 : Access
  reduce_cmd : ReduceCmd
  reduce_res : Option Access
  reduce_op : AluOp
  range_start : Nat
  on_false_value : Float
  dtype : Option Dtype
deriving Repr

-- Reciprocal operation
structure Reciprocal  where
  data : Access
  dtype : Option Dtype
deriving Repr

-- Scalar-tensor-tensor operation
structure ScalarTensorTensor  where
  data : Access
  op0 : AluOp
  operand0 : Operand
  op1 : AluOp
  operand1 : Access
  reverse0 : Bool
  reverse1 : Bool
  dtype : Option Dtype
deriving Repr

-- Tensor copy
structure TensorCopy  where
  src : Access
  dtype : Option Dtype
  engine : Engine
deriving Repr

-- Dynamic destination tensor copy
structure TensorCopyDynamicDst  where
  dst : Access
  src : Access
  dtype : Option Dtype
  engine : Engine
deriving Repr

-- Dynamic source tensor copy
structure TensorCopyDynamicSrc  where
  src : Access
  dtype : Option Dtype
  engine : Engine
deriving Repr

-- Predicated tensor copy
structure TensorCopyPredicated  where
  src : Operand
  dst : Access
  predicate : Access
  dtype : Option Dtype
  reverse_pred : Bool
deriving Repr

-- Partition reduce
structure TensorPartitionReduce  where
  dst : Access
  op : AluOp
  data : Access
  dtype : Option Dtype
deriving Repr

-- Tensor reduce
structure TensorReduce  where
  dst : Access
  op : AluOp
  data : Access
  axis : List Nat
  dtype : Option Dtype
  negate : Bool
  keepdims : Bool
deriving Repr

-- Tensor-scalar operation
structure TensorScalar  where
  dst : Access
  data : Access
  op0 : AluOp
  operand0 : Operand
  reverse0 : Bool
  op1 : Option AluOp
  operand1 : Option Operand
  reverse1 : Bool
  dtype : Option Dtype
  engine : Engine
deriving Repr

-- Tensor-scalar with reduction
structure TensorScalarReduce  where
  dst : Access
  data : Access
  op0 : AluOp
  operand0 : Operand
  reduce_op : AluOp
  reduce_res : Access
  reverse0 : Bool
  dtype : Option Dtype
deriving Repr

-- Tensor-tensor operation
structure TensorTensor  where
  dst : Access
  data1 : Access
  data2 : Access
  op : AluOp
  dtype : Option Dtype
  engine : Engine
deriving Repr

-- Tensor-tensor scan
structure TensorTensorScan  where
  dst : Access
  data0 : Access
  data1 : Access
  initial : Operand
  op0 : AluOp
  op1 : AluOp
  reverse0 : Bool
  reverse1 : Bool
  dtype : Option Dtype
deriving Repr

-- Find index8 operation
structure NcFindIndex8  where
  dst : Access
  data : Access
  vals : Access
  dtype : Option Dtype
deriving Repr

-- Match replace8 operation
structure NcMatchReplace8  where
  dst : Access
  data : Access
  vals : Access
  imm : Float
  dst_idx : Option Access
  dtype : Option Dtype
deriving Repr

-- Custom operation
structure BuiltinCustomOp  where
  dsts : List Access
  function_name : String
  lib_file_name : String
  ulib_to_ucode_version : String
  ulib_to_isa_version : String
  srcs : List Access
deriving Repr

inductive Operation  where
  | arg (n : Nat)
  | const (t: Tensor) (shape : Shape) (dtype : Dtype)
  | activation (_ : Activation)
  | activation_reduce (_ : ActivationReduce)
  | affine_select (_ : AffineSelect)
  | bn_aggr (_ : BnAggr)
  | bn_stats (_ : BnStats)
  | dma_copy (_ : DmaCopy)
  | dma_transpose (_ : DmaTranspose)
  | dropout (_ : Dropout)
  | iota (_ : Iota)
  | local_gather (_ : LocalGather)
  | max8 (_ : Max8)
  | memset (_ : Memset)
  | nc_matmul (_ : NcMatmul)
  | nc_stream_shuffle (_ : NcStreamShuffle)
  | nc_transpose (_ : NcTranspose)
  | range_select (_ : RangeSelect)
  | reciprocal (_ : Reciprocal)
  | scalar_tensor_tensor (_ : ScalarTensorTensor)
  | tensor_copy (_ : TensorCopy)
  | tensor_copy_dynamic_dst (_ : TensorCopyDynamicDst)
  | tensor_copy_dynamic_src (_ : TensorCopyDynamicSrc)
  | tensor_copy_predicated (_ : TensorCopyPredicated)
  | tensor_partition_reduce (_ : TensorPartitionReduce)
  | tensor_reduce (_ : TensorReduce)
  | tensor_scalar (_ : TensorScalar)
  | tensor_scalar_reduce (_ : TensorScalarReduce)
  | tensor_tensor (_ : TensorTensor)
  | tensor_tensor_scan (_ : TensorTensorScan)
  | nc_find_index8 (_ : NcFindIndex8)
  | nc_match_replace8 (_ : NcMatchReplace8)
  | builtin_custom_op (_ : BuiltinCustomOp)

/-

TODO: How to handle function calls?

TODO: How to handle looping and conditionals?

TODO: How to handle inline assembly?

TODO: Add simple expression language for registers

Note: no return statement. We assume return values will be stored in HBM
locations marked as outputs.
-/
inductive Statement  where
  | comment (msg : String)
  | op (op : Operation )
