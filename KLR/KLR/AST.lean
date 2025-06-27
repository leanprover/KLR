-- NKI ISA (Instruction Set Architecture) definitions translated from Python
-- For original, see https://github.com/aws-neuron/aws-neuron-sdk/blob/094394bc464872f3387d315ae446576583660422/general/nki/api/nki/isa/__init__.py

namespace KLR.KLR

-- Enums from the original Python code

inductive DgeMode : Type where
  | none : DgeMode      -- Not using DGE
  | swdge : DgeMode     -- Software DGE
  | hwdge : DgeMode     -- Hardware DGE
  | unknown : DgeMode   -- Unknown DGE mode, let compiler decide
deriving Repr, DecidableEq

inductive Engine : Type where
  | tensor : Engine     -- Tensor Engine
  | vector : Engine     -- Vector Engine
  | scalar : Engine     -- Scalar Engine
  | gpsimd : Engine     -- GpSIMD Engine
  | sync : Engine       -- Sync Engine
  | unknown : Engine    -- Unknown Engine
deriving Repr, DecidableEq

inductive NcVersion : Type where
  | gen2 : NcVersion    -- Trn1/Inf2 target
  | gen3 : NcVersion    -- Trn2 target
deriving Repr, DecidableEq

inductive OobMode : Type where
  | error : OobMode     -- Raise error on out-of-bounds
  | skip : OobMode      -- Skip out-of-bounds operations
deriving Repr, DecidableEq

inductive ReduceCmd : Type where
  | idle : ReduceCmd           -- Not using accumulator registers
  | reset : ReduceCmd          -- Reset accumulator registers
  | reset_reduce : ReduceCmd   -- Reset then accumulate
  | reduce : ReduceCmd         -- Keep accumulating
deriving Repr, DecidableEq

-- FP32 constants structure
structure Fp32Constants where
  min : Float  -- FP32 minimum value bit pattern
deriving Repr

-- Data types that can be used in operations
inductive DataType : Type where
  | float32 : DataType
  | float16 : DataType
  | bfloat16 : DataType
  | float8_e4m3 : DataType
  | float8_e5m2 : DataType
  | tfloat32 : DataType
  | int32 : DataType
  | int16 : DataType
  | int8 : DataType
  | uint32 : DataType
  | uint16 : DataType
  | uint8 : DataType
deriving Repr, DecidableEq

-- Tile shape representation
structure TileShape where
  partition_axis : Nat
  free_axes : List Nat
deriving Repr, DecidableEq

-- Tile reference (can be in SBUF or PSUM)
inductive BufferType : Type where
  | sbuf : BufferType   -- SBUF memory
  | psum : BufferType   -- PSUM memory
deriving Repr, DecidableEq

structure Tile where
  shape : TileShape
  dtype : DataType
  buffer : BufferType
deriving Repr, DecidableEq

-- Math operators
inductive MathOp : Type where
  | add : MathOp
  | subtract : MathOp
  | multiply : MathOp
  | divide : MathOp
  | maximum : MathOp
  | minimum : MathOp
  | power : MathOp
  | bitwise_and : MathOp
  | bitwise_or : MathOp
  | equal : MathOp
  | less : MathOp
  | less_equal : MathOp
  | greater : MathOp
  | greater_equal : MathOp
deriving Repr, DecidableEq

-- Activation functions
inductive ActivationFunc : Type where
  | relu : ActivationFunc
  | sigmoid : ActivationFunc
  | tanh : ActivationFunc
  | gelu : ActivationFunc
  | exp : ActivationFunc
  | log : ActivationFunc
  | sqrt : ActivationFunc
  | rsqrt : ActivationFunc
deriving Repr, DecidableEq

-- Operand types (scalar or vector)
inductive Operand : Type where
  | scalar : Float → Operand
  | vector : Tile → Operand
  | tile : Tile → Operand
deriving Repr

-- Mask for conditional execution
inductive Mask : Type where
  | none : Mask
  | predicate : Tile → Mask  -- Boolean predicate tile
deriving Repr

-- Main instruction types representing the AST nodes

inductive Instruction : Type where
  -- Activation instruction
  | activation :
      (op : ActivationFunc) →
      (data : Tile) →
      (bias : Option Operand) →
      (scale : Operand) →
      (reduce_op : Option MathOp) →
      (reduce_res : Option Tile) →
      (reduce_cmd : ReduceCmd) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Activation with reduction
  | activation_reduce :
      (op : ActivationFunc) →
      (data : Tile) →
      (reduce_op : MathOp) →
      (reduce_res : Tile) →
      (bias : Option Operand) →
      (scale : Operand) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Affine select operation
  | affine_select :
      (pred : Tile) →  -- Affine expression predicate
      (on_true_tile : Tile) →
      (on_false_value : Float) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Batch normalization aggregation
  | bn_aggr :
      (data : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Batch normalization statistics
  | bn_stats :
      (data : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- DMA copy operation
  | dma_copy :
      (dst : Tile) →
      (src : Tile) →
      (mask : Mask) →
      (dst_rmw_op : Option MathOp) →
      (oob_mode : OobMode) →
      (dge_mode : DgeMode) →
      Instruction

  -- DMA transpose
  | dma_transpose :
      (src : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Dropout operation
  | dropout :
      (data : Tile) →
      (prob : Operand) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Iota (constant generation)
  | iota :
      (expr : Tile) →  -- Affine expression
      (dtype : DataType) →
      (mask : Mask) →
      Instruction

  -- Local gather operation
  | local_gather :
      (src_buffer : Tile) →
      (index : Tile) →
      (num_elem_per_idx : Nat) →
      (num_valid_indices : Option Nat) →
      (mask : Mask) →
      Instruction

  -- Max8 operation
  | max8 :
      (src : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Memory set operation
  | memset :
      (shape : TileShape) →
      (value : Float) →
      (dtype : DataType) →
      (mask : Mask) →
      (engine : Engine) →
      Instruction

  -- Matrix multiplication
  | nc_matmul :
      (stationary : Tile) →
      (moving : Tile) →
      (is_stationary_onezero : Bool) →
      (is_moving_onezero : Bool) →
      (is_transpose : Bool) →
      (tile_position : Option (Nat × Nat)) →
      (tile_size : Option (Nat × Nat)) →
      (mask : Mask) →
      Instruction

  -- Stream shuffle
  | nc_stream_shuffle :
      (src : Tile) →
      (dst : Tile) →
      (shuffle_mask : List Nat) →
      (dtype : Option DataType) →
      (mask : Mask) →
      Instruction

  -- Transpose operation
  | nc_transpose :
      (data : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      (engine : Engine) →
      Instruction

  -- Range select operation
  | range_select :
      (on_true_tile : Tile) →
      (comp_op0 : MathOp) →
      (comp_op1 : MathOp) →
      (bound0 : Tile) →
      (bound1 : Tile) →
      (reduce_cmd : ReduceCmd) →
      (reduce_res : Option Tile) →
      (reduce_op : MathOp) →
      (range_start : Nat) →
      (on_false_value : Float) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Reciprocal operation
  | reciprocal :
      (data : Tile) →
      (dtype : Option DataType) →
      (mask : Mask) →
      Instruction

  -- Scalar-tensor-tensor operation
  | scalar_tensor_tensor :
      (data : Tile) →
      (op0 : MathOp) →
      (operand0 : Operand) →
      (op1 : MathOp) →
      (operand1 : Tile) →
      (reverse0 : Bool) →
      (reverse1 : Bool) →
      (dtype : Option DataType) →
      (mask : Mask) →
      Instruction

  -- Tensor copy
  | tensor_copy :
      (src : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      (engine : Engine) →
      Instruction

  -- Dynamic destination tensor copy
  | tensor_copy_dynamic_dst :
      (dst : Tile) →
      (src : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      (engine : Engine) →
      Instruction

  -- Dynamic source tensor copy
  | tensor_copy_dynamic_src :
      (src : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      (engine : Engine) →
      Instruction

  -- Predicated tensor copy
  | tensor_copy_predicated :
      (src : Operand) →
      (dst : Tile) →
      (predicate : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      (reverse_pred : Bool) →
      Instruction

  -- Partition reduce
  | tensor_partition_reduce :
      (op : MathOp) →
      (data : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Tensor reduce
  | tensor_reduce :
      (op : MathOp) →
      (data : Tile) →
      (axis : List Nat) →
      (mask : Mask) →
      (dtype : Option DataType) →
      (negate : Bool) →
      (keepdims : Bool) →
      Instruction

  -- Tensor-scalar operation
  | tensor_scalar :
      (data : Tile) →
      (op0 : MathOp) →
      (operand0 : Operand) →
      (reverse0 : Bool) →
      (op1 : Option MathOp) →
      (operand1 : Option Operand) →
      (reverse1 : Bool) →
      (dtype : Option DataType) →
      (mask : Mask) →
      (engine : Engine) →
      Instruction

  -- Tensor-scalar with reduction
  | tensor_scalar_reduce :
      (data : Tile) →
      (op0 : MathOp) →
      (operand0 : Operand) →
      (reduce_op : MathOp) →
      (reduce_res : Tile) →
      (reverse0 : Bool) →
      (dtype : Option DataType) →
      (mask : Mask) →
      Instruction

  -- Tensor-tensor operation
  | tensor_tensor :
      (data1 : Tile) →
      (data2 : Tile) →
      (op : MathOp) →
      (dtype : Option DataType) →
      (mask : Mask) →
      (engine : Engine) →
      Instruction

  -- Tensor-tensor scan
  | tensor_tensor_scan :
      (data0 : Tile) →
      (data1 : Tile) →
      (initial : Operand) →
      (op0 : MathOp) →
      (op1 : MathOp) →
      (reverse0 : Bool) →
      (reverse1 : Bool) →
      (dtype : Option DataType) →
      (mask : Mask) →
      Instruction

  -- Find index8 operation
  | nc_find_index8 :
      (data : Tile) →
      (vals : Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Match replace8 operation
  | nc_match_replace8 :
      (data : Tile) →
      (vals : Tile) →
      (imm : Float) →
      (dst_idx : Option Tile) →
      (mask : Mask) →
      (dtype : Option DataType) →
      Instruction

  -- Custom operation
  | builtin_custom_op :
      (function_name : String) →
      (lib_file_name : String) →
      (ulib_to_ucode_version : String) →
      (ulib_to_isa_version : String) →
      (srcs : List Tile) →
      (dsts : List Tile) →
      Instruction

deriving Repr

-- Helper functions and constants

def fp32 : Fp32Constants := ⟨-3.4028235e+38⟩

def dma_engine : Engine := Engine.unknown
def gpsimd_engine : Engine := Engine.gpsimd
def scalar_engine : Engine := Engine.scalar
def tensor_engine : Engine := Engine.tensor
def unknown_engine : Engine := Engine.unknown
def vector_engine : Engine := Engine.vector

-- Function to get NC version (would be implemented based on context)
def get_nc_version : NcVersion := NcVersion.gen2

end KLR.KLR
