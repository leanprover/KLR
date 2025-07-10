/-
The definition of the KLR AST

This is based on the nki.isa API, which can be seen at
https://github.com/aws-neuron/aws-neuron-sdk/blob/094394bc464872f3387d315ae446576583660422/general/nki/api/nki/isa/__init__.py

-/

import TensorLib.Tensor
import TensorLib.Shape
import TensorLib.Dtype
import KLR.KLR.Tensor

open TensorLib(Tensor Shape Dtype)

namespace KLR.KLR

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
