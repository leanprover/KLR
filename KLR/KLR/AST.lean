/-
The definition of the KLR AST

This is based on the nki.isa API, which can be seen at
https://github.com/aws-neuron/aws-neuron-sdk/blob/094394bc464872f3387d315ae446576583660422/general/nki/api/nki/isa/__init__.py

Many structures here are parameterized by `Atom` and `Engine` types.
An `Atom` corresponds to the input and output locations for operands. For example,
in a high level language `Atom` would be a variable name, while in a low level language
it could be a physical access pattern.
An `Engine` corresponds to the execution engine used for an operation. Before engine
selection, it would be the unit type. After engine selection, it would be a sum type
indicating which engine is used.
-/

import TensorLib.Tensor
import TensorLib.Shape
import TensorLib.Dtype

open TensorLib(Tensor Shape Dtype)

namespace KLR.KLR

inductive DgeMode where
  | none      -- Not using DGE
  | swdge     -- Software DGE
  | hwdge     -- Hardware DGE
  | unknown   -- Unknown DGE mode, let compiler decide
deriving Repr, DecidableEq

inductive Trn2Engine where
  | tensor     -- Tensor Engine
  | vector     -- Vector Engine
  | scalar     -- Scalar Engine
  | gpsimd     -- GpSIMD Engine
  | sync       -- Sync Engine
deriving Repr, DecidableEq, Inhabited

inductive NcVersion where
  | gen2    -- Trn1/Inf2 target
  | gen3    -- Trn2 target
deriving Repr, DecidableEq

inductive OobMode where
  | error     -- Raise error on out-of-bounds
  | skip      -- Skip out-of-bounds operations
deriving Repr, DecidableEq

inductive ReduceCmd where
  | idle           -- Not using accumulator registers
  | reset          -- Reset accumulator registers
  | reset_reduce   -- Reset then accumulate
  | reduce         -- Keep accumulating
deriving Repr, DecidableEq

-- FP32 constants structure
structure Fp32Constants where
  min : Float  -- FP32 minimum value bit pattern
deriving Repr

-- Data types that can be used in operations
inductive DataType where
  | float32
  | float16
  | bfloat16
  | float8_e4m3
  | float8_e5m2
  | tfloat32
  | int32
  | int16
  | int8
  | uint32
  | uint16
  | uint8
deriving Repr, DecidableEq, Inhabited

abbrev Atom := String  -- Variable names

-- Math operators
inductive MathOp where
  | add
  | subtract
  | multiply
  | divide
  | maximum
  | minimum
  | power
  | bitwise_and
  | bitwise_or
  | equal
  | less
  | less_equal
  | greater
  | greater_equal
deriving Repr, DecidableEq

-- Activation functions
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
-- TODO: how does this interact with being generic over Atom?
inductive Operand (Atom : Type) where
  | scalar (_ : Float32)
  | vector (_ : Atom)
  | tile  (_ : Atom)
deriving Repr, Inhabited

-- Activation instruction
structure Activation (Atom Engine : Type) where
  dst : Atom
  op : ActivationFunc
  data : Atom
  bias : Option (Operand Atom)
  scale : Operand Atom
  reduce_op : Option MathOp
  reduce_res : Option Atom
  reduce_cmd : ReduceCmd
  dtype : Option DataType
deriving Repr

-- Activation with reduction
structure ActivationReduce (Atom Engine : Type) where
  dst : Atom
  op : ActivationFunc
  data : Atom
  reduce_op : MathOp
  reduce_res : Atom
  bias : Option (Operand Atom)
  scale : Operand Atom
  dtype : Option DataType
deriving Repr

-- Affine select operation
structure AffineSelect (Atom Engine : Type) where
  dst : Atom
  pred : Atom
  on_true_tile : Atom
  on_false_value : Float
  dtype : Option DataType
deriving Repr

-- Batch normalization aggregation
structure BnAggr (Atom Engine : Type) where
  dst : Atom
  data : Atom
  dtype : Option DataType
deriving Repr

-- Batch normalization statistics
structure BnStats (Atom Engine : Type) where
  dst : Atom
  data : Atom
  dtype : Option DataType
deriving Repr

-- DMA copy operation
structure DmaCopy (Atom : Type) where
  dst : Atom
  src : Atom
  dst_rmw_op : Option MathOp
  oob_mode : OobMode
  dge_mode : DgeMode
deriving Repr

-- DMA transpose
structure DmaTranspose (Atom : Type) where
  src : Atom
  dtype : Option DataType
deriving Repr

-- Dropout operation
structure Dropout (Atom : Type) where
  data : Atom
  prob : Operand Atom
  dtype : Option DataType
deriving Repr

-- Iota (Atom : Type)
structure Iota (Atom : Type) where
  expr : Atom  -- Affine expression (dtype : DataType)
deriving Repr

-- Local gather operation
structure LocalGather (Atom : Type) where
  src_buffer : Atom
  index : Atom
  num_elem_per_idx : Nat
  num_valid_indices : Option Nat
deriving Repr

-- Max8 operation
structure Max8 (Atom : Type) where
  src : Atom
  dtype : Option DataType
deriving Repr

-- Memory set operation
structure Memset (Atom Engine : Type) where
  shape : Shape
  value : Float
  dtype : DataType
  engine : Engine
deriving Repr

-- Matrix multiplication
structure NcMatmul (Atom : Type) where
  stationary : Atom
  moving : Atom
  is_stationary_onezero : Bool
  is_moving_onezero : Bool
  is_transpose : Bool
  tile_position : Option (Nat × Nat)
  tile_size : Option (Nat × Nat)
deriving Repr

-- Stream shuffle
structure NcStreamShuffle (Atom : Type) where
  src : Atom
  shuffle_mask : List Nat
  dtype : Option DataType
deriving Repr

-- Transpose operation
structure NcTranspose (Atom Engine : Type) where
  data : Atom
  dtype : Option DataType
  engine : Engine
deriving Repr

-- Range select operation
structure RangeSelect (Atom : Type) where
  on_true_tile : Atom
  comp_op0 : MathOp
  comp_op1 : MathOp
  bound0 : Atom
  bound1 : Atom
  reduce_cmd : ReduceCmd
  reduce_res : Option Atom
  reduce_op : MathOp
  range_start : Nat
  on_false_value : Float
  dtype : Option DataType
deriving Repr

-- Reciprocal operation
structure Reciprocal (Atom : Type) where
  data : Atom
  dtype : Option DataType
deriving Repr

-- Scalar-tensor-tensor operation
structure ScalarTensorTensor (Atom : Type) where
  data : Atom
  op0 : MathOp
  operand0 : Operand Atom
  op1 : MathOp
  operand1 : Atom
  reverse0 : Bool
  reverse1 : Bool
  dtype : Option DataType
deriving Repr

-- Tensor copy
structure TensorCopy (Atom Engine : Type) where
  src : Atom
  dtype : Option DataType
  engine : Engine
deriving Repr

-- Dynamic destination tensor copy
structure TensorCopyDynamicDst (Atom Engine : Type) where
  dst : Atom
  src : Atom
  dtype : Option DataType
  engine : Engine
deriving Repr

-- Dynamic source tensor copy
structure TensorCopyDynamicSrc (Atom Engine : Type) where
  src : Atom
  dtype : Option DataType
  engine : Engine
deriving Repr

-- Predicated tensor copy
structure TensorCopyPredicated (Atom : Type) where
  src : Operand Atom
  dst : Atom
  predicate : Atom
  dtype : Option DataType
  reverse_pred : Bool
deriving Repr

-- Partition reduce
structure TensorPartitionReduce (Atom : Type) where
  dst : Atom
  op : MathOp
  data : Atom
  dtype : Option DataType
deriving Repr

-- Tensor reduce
structure TensorReduce (Atom : Type) where
  dst : Atom
  op : MathOp
  data : Atom
  axis : List Nat
  dtype : Option DataType
  negate : Bool
  keepdims : Bool
deriving Repr

-- Tensor-scalar operation
structure TensorScalar (Atom Engine : Type) where
  dst : Atom
  data : Atom
  op0 : MathOp
  operand0 : Operand Atom
  reverse0 : Bool
  op1 : Option MathOp
  operand1 : Option (Operand Atom)
  reverse1 : Bool
  dtype : Option DataType
  engine : Engine
deriving Repr

-- Tensor-scalar with reduction
structure TensorScalarReduce (Atom : Type) where
  dst : Atom
  data : Atom
  op0 : MathOp
  operand0 : Operand Atom
  reduce_op : MathOp
  reduce_res : Atom
  reverse0 : Bool
  dtype : Option DataType
deriving Repr

-- Tensor-tensor operation
structure TensorTensor (Atom Engine : Type) where
  dst : Atom
  data1 : Atom
  data2 : Atom
  op : MathOp
  dtype : Option DataType
  engine : Engine
deriving Repr

-- Tensor-tensor scan
structure TensorTensorScan (Atom : Type) where
  dst : Atom
  data0 : Atom
  data1 : Atom
  initial : Operand Atom
  op0 : MathOp
  op1 : MathOp
  reverse0 : Bool
  reverse1 : Bool
  dtype : Option DataType
deriving Repr

-- Find index8 operation
structure NcFindIndex8 (Atom : Type) where
  dst : Atom
  data : Atom
  vals : Atom
  dtype : Option DataType
deriving Repr

-- Match replace8 operation
structure NcMatchReplace8 (Atom : Type) where
  dst : Atom
  data : Atom
  vals : Atom
  imm : Float
  dst_idx : Option Atom
  dtype : Option DataType
deriving Repr

-- Custom operation
structure BuiltinCustomOp (Atom : Type) where
  dsts : List Atom
  function_name : String
  lib_file_name : String
  ulib_to_ucode_version : String
  ulib_to_isa_version : String
  srcs : List Atom
deriving Repr

inductive Operation (Atom Engine : Type) where
  | arg (n : Nat)
  | const (t: Tensor) (shape : Shape) (dtype : Dtype)
  | activation (_ : Activation Atom Engine)
  | activation_reduce (_ : ActivationReduce Atom Engine)
  | affine_select (_ : AffineSelect Atom Engine)
  | bn_aggr (_ : BnAggr Atom Engine)
  | bn_stats (_ : BnStats Atom Engine)
  | dma_copy (_ : DmaCopy Atom)
  | dma_transpose (_ : DmaTranspose Atom)
  | dropout (_ : Dropout Atom)
  | iota (_ : Iota Atom)
  | local_gather (_ : LocalGather Atom)
  | max8 (_ : Max8 Atom)
  | memset (_ : Memset Atom Engine)
  | nc_matmul (_ : NcMatmul Atom)
  | nc_stream_shuffle (_ : NcStreamShuffle Atom)
  | nc_transpose (_ : NcTranspose Atom Engine)
  | range_select (_ : RangeSelect Atom)
  | reciprocal (_ : Reciprocal Atom)
  | scalar_tensor_tensor (_ : ScalarTensorTensor Atom)
  | tensor_copy (_ : TensorCopy Atom Engine)
  | tensor_copy_dynamic_dst (_ : TensorCopyDynamicDst Atom Engine)
  | tensor_copy_dynamic_src (_ : TensorCopyDynamicSrc Atom Engine)
  | tensor_copy_predicated (_ : TensorCopyPredicated Atom)
  | tensor_partition_reduce (_ : TensorPartitionReduce Atom)
  | tensor_reduce (_ : TensorReduce Atom)
  | tensor_scalar (_ : TensorScalar Atom Engine)
  | tensor_scalar_reduce (_ : TensorScalarReduce Atom)
  | tensor_tensor (_ : TensorTensor Atom Engine)
  | tensor_tensor_scan (_ : TensorTensorScan Atom)
  | nc_find_index8 (_ : NcFindIndex8 Atom)
  | nc_match_replace8 (_ : NcMatchReplace8 Atom)
  | builtin_custom_op (_ : BuiltinCustomOp Atom)

/-

TODO: How to handle function calls?

TODO: How to handle looping and conditionals?

TODO: How to handle inline assembly?

TODO: Add simple expression language for registers

Note: no return statement. We assume return values will be stored in HBM
locations marked as outputs.
-/
inductive Statement (Atom Engine : Type) where
  | comment (msg : String)
  | op (op : Operation Atom Engine)
