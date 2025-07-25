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

import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Tensor

namespace KLR.Trace.Isa
open KLR.Core

private def maskNotSupported := "mask parameter is not supported"

def converRevOps (reverse0 : Bool) (reverse1 : Bool) : TensorScalarReverseOps :=
  match reverse0, reverse1 with
    | false, false => .none
    | true, false => .first
    | false, true => .second
    | true, true => .both

def immediateToValue (imm : Immediate) : Value :=
  match imm with
  | .int i => .int i.toInt
  | .float f => .float f.toFloat
  | .register r =>  .var s!"reg{r}" -- FIXME
  | .pointer => .var "ptr" -- FIXME

def engineToValue (engine : Engine) : Value :=
  match engine with
  | .unassigned => .var "Unknown Engine"
  | .act => .var "Unknown Engine" -- FIXME
  | .dma => .var "Unknown Engine" -- FIXME
  | .dve => .var "Vector Engine"
  | .pe => .var "Tensor Engine"
  | .pool => .var "Unknown Engine"
  | .sp => .var "Scalar Engine"

def accumCmdToValue (ac : AccumCmd) : Value :=
  match ac with
  | .Idle => .int 0
  | .Zero => .int 1
  | .Accumulate => .int 2
  | .ZeroAccumulate => .int 3
  | .LoadAccumulate => .int 4 -- FIXME

-- set_option linter.unusedVariables false

nki nc_matmul
 (dst : Access)
 (stationary : Access)
 -- kwargs
 (moving : Access)
 (is_stationary_onezero : Bool := false)
 (is_moving_zero : Bool := false)
 (is_transpose : Bool := false)
 (tile_position : List Nat := [])
 (tile_size : List Nat := [])
 (mask : Option Immediate := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper $ .ncMatMul {
      dst := .abstract dst
      stationary := .abstract stationary
      moving := .abstract moving
      isStationaryOneZero := is_stationary_onezero
      isMovingZero := is_moving_zero
      isTranspose := is_transpose
      tilePosition := tile_position
      tileSize := tile_size
      }
    return .none

nki nc_transpose
 (dst : Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned) := do
  if mask.isSome then
    throw maskNotSupported
  Trace.add_stmt $ .oper $ .transpose {
    dst := .abstract dst,
    src := .abstract data,
    dtype := dtype,
    engine := engine,
  }
  return .none

nki activation
 (dst : Access)
 (op : ActivationFunc)
 (data : Access)
 -- kwargs
 (bias : Immediate := .float 0) -- Also can be a tensor. Default is none
 (scale : Immediate := .float 1.0) -- This also can accept a tensor
 (reduce_op : Option AluOp := none)
 (reduce_res : Option Access := none)
 (reduce_cmd : AccumCmd := .Idle)
 (mask : Option Immediate := none) := do
  if mask.isSome then
    throw maskNotSupported
  Trace.add_stmt $ .oper $ .activate {
    dst := .abstract dst,
    src := .abstract data,
    accumulatorCmd := reduce_cmd,
    activationFunc := op,
    scale := scale,
    bias := bias,
    reduceOp := reduce_op,
    reduceRes := reduce_res.map .abstract,
  }
  return .none

nki activation_reduce
 (dst: Access)
 (op : ActivationFunc)
 (data : Access)
 -- kwargs
 (reduce_op : Option AluOp := none)
 (reduce_res : Option Access := none)
 (bias : List Immediate := [])
 (scale : Sum Immediate Access := .inl (.float 1.0))
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper $ .activationReduce {
      dst := .abstract dst,
      op := op,
      data := .abstract data,
      bias := bias,
      reduceOp := reduce_op,
      reduceRes := reduce_res.map .abstract
      scale := match scale with
      | .inl i => .imm i
      | .inr t => .tensor $ .abstract t,
      dtype := dtype,
    }
    return .none

nki tensor_reduce
  (dst: Access)
  (op : AluOp)
  (data : Access)
  (axis : Sum Int (List Int))
  -- kwargs
  (mask : Option Immediate := none)
  (dtype : Option Dtype := none)
  (negate : Bool := false)
  (keepdims : Bool := false) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper $ .tensorReduce {
      dst  := .abstract dst,
      src  := .abstract data,
      op   := op,
      axis := match axis with
        | .inl l => .ax l
        | .inr r => .axs r,
      dtype := dtype,
      negated := negate,
      keepdims := keepdims
    }
    return .none

nki tensor_partition_reduce
  (dst: Access)
  (op : AluOp)
  (data : Access)
  -- kwargs
  (mask : Option Immediate := none)
  (dtype : Option Dtype := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper $ .tensorPartitionReduce {
      dst := .abstract dst,
      op := op,
      data := .abstract data
      dtype := dtype
    }
    return .none

nki tensor_tensor
 (dst: Access)
 (data1 : Access)
 (data2 : Access)
 (op : AluOp)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper $ .tensorTensor {
      dst := .abstract dst,
      src0 := .abstract data1,
      src1 := .abstract data2,
      op := op,
      dtype := dtype,
      engine := engine
    }
    return .none

nki tensor_tensor_scan
 (dst: Access)
 (data0 : Access)
 (data1 : Access)
 (initial : Sum Immediate Access)
 (op0 : AluOp)
 (op1 : AluOp)
 (reverse0 : Bool := false)
 (reverse1 : Bool := false)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none) := do
    if mask.isSome then
      throw maskNotSupported
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1
    Trace.add_stmt $ .oper $ .tensorTensorScan {
        dst := .abstract dst
        src0 := .abstract data0
        src1 := .abstract data1
        op0 := op0
        op1 := op1
        reverseOperands := rev
        initial := match initial with
          | .inl l => .imm l
          | .inr t => .tile $ .abstract t,
        dtype := dtype
    }
    return .none

nki scalar_tensor_tensor
 (dst : Access)
 -- kwargs
 (data : Access)
 (op0 : AluOp)
 (operand0 : Sum Immediate Access)
 (op1 : AluOp)
 (operand1 : Sum Immediate Access)
 (reverse0 : Bool := false)
 (reverse1 : Bool := false)
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none) := do
    if mask.isSome then throw maskNotSupported
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1
    Trace.add_stmt $ .oper $ .scalarTensorTensor {
        dst := .abstract dst
        data := .abstract data
        src0 := match operand0 with
          | .inl i => .imm i
          | .inr t => .tile $ .abstract t
        src1 := match operand1 with
          | .inl i => .imm i
          | .inr t => .tile $ .abstract t
        op0  := op0
        op1  := op1
        reverseOperands := rev
        dtype := dtype
    }
    return .none

nki tensor_scalar
 (dst: Access)
 (data : Access)
 (op0 : AluOp)
 (operand0 : Sum Immediate Access)
 (reverse0 : Bool := false)
 (op1 : Option AluOp := none)
 (operand1 : Option (Sum Immediate Access) := none)
 (reverse1 : Bool := false)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned) := do
    if mask.isSome then throw maskNotSupported
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1
    Trace.add_stmt $ .oper $ .tensorScalar {
      dst := .abstract dst,
      src := .abstract data
      operand0 := match operand0 with
        | .inl i => .imm i
        | .inr t => .tile $ .abstract t
      op0 := op0
      operand1 := match operand1 with
        | some (.inl i) => some $ .imm i
        | some (.inr t) => some $ .tile $ .abstract t
        | none => none
      op1 := op1
      reverse := rev
      engine := engine
      dtype := dtype
    }
    return .none

nki tensor_scalar_reduce
 (dst : Access)
 -- kwargs
 (data : Access)
 (op0 : AluOp)
 (operand0 : Sum Immediate Access)
 (reduce_op : AluOp)
 (reduce_res : Access)
 (reverse0 : Bool := false)
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .tensorScalarReduce {
        dst := .abstract dst
        src := .abstract data
        operand0 := match operand0 with
          | .inl i => .imm i
          | .inr t => .tile $ .abstract t
        op0 := op0
        reduceOp := reduce_op
        reduceRes := .abstract reduce_res
        reverse0 := reverse0
        dtype := dtype
    }
    return .none

nki tensor_copy
 (dst: Access)
 (src : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .copy {
      dst := .abstract dst
      src := .abstract src
      dtype := dtype
      engine := engine
    }
    return .none

nki tensor_copy_dynamic_src
 (dst : Access)
 (src : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .copy {
      dst := .abstract dst
      src := .abstract src
      dtype := dtype
      engine := engine
    }
    return .none

nki tensor_copy_dynamic_dst
 -- kwargs
 (dst : Access)
 (src : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .copy {
      dst := .abstract dst
      src := .abstract src
      dtype := dtype
      engine := engine
    }
    return .none

nki tensor_copy_predicated
 (dst : Access)
 -- kwargs
 (src : Access)
 (predicate : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (reverse_pred : Bool := false) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .copyPredicated  {
      dst := .abstract dst,
      src := .abstract src,
      predicate := .abstract predicate,
      dtype := dtype,
      reversePred := reverse_pred,
    }
    return .none

nki reciprocal
 (dst: Access)
 (data : Access)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .reciprocal {
      dst := .abstract dst
      src := .abstract data
      dtype := dtype
    }
    return .none

nki iota
 (dst: Access)
 (_expr : Int) -- TODO: Placeholder. Figure out this type
 --
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .iota {
      dst := .abstract dst
      pattern := ⟨ 0, [] ⟩  -- Fixme once we have conversion from expr to pattern
      dtype := dtype
    }
    return .none

nki dropout
 (dst: Access)
 (data : Access)
 (prob : Sum Immediate Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .dropout {
        dst       := .abstract dst,
        src       := .abstract data,
        threshold := match prob with
          | .inl i => .imm i
          | .inr t => .tile $ .abstract t
        thresholdType := .KeepRate
        dtype         := dtype,
    }
    return .none

nki affine_select
 (dst: Access)
 (_pred : Int) -- TODO Placeholder. Figure out this type
 (on_true_tile : Access)
 (on_false_value : Immediate)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .affineSelect {
      dst := .abstract dst,
      fillMode := .Eq, -- TODO figure out how to get it from predicate
      onTrueTile := .abstract on_true_tile,
      onFalseValue := on_false_value,
      dtype := dtype,
    }
    return .none

-- nki range_select
--  (dst: Access)
--  --
--  (on_true_tile : Access)
--  (comp_op0 : AluOp)
--  (comp_op1 : AluOp)
--  (bound0 : Access)
--  (bound1 : Access)
--  (reduce_cmd : AccumCmd := AccumCmd.Idle)
--  (reduce_res : Option Access := none)
--  (reduce_op : AluOp := .max)
--  (range_start : Immediate := .float 0)
--  (on_false_value : Immediate := .float 0)
--  (mask : Option Immediate := none)
--  (dtype : Option Dtype := none) := do
--     if mask.isSome then throw maskNotSupported
--     return .none

nki memset
 (dst: Access)
 (shape : Shape)
 (value : Immediate)
 (dtype : Dtype)
 -- kwargs
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .memSet {
      dst    := .abstract dst,
      value  := value,
      count  := shape.freeElements,
      dtype  := dtype,
      engine := engine
    }
    return .none

nki bn_stats
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask: Option Immediate := none)
 (dtype: Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .batchNormStats {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dtype
    }
    return .none

nki bn_aggr
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .batchNormAggregate {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dtype
    }
    return .none

nki local_gather
 (dst: Access)
 (src_buffer : Access)
 (index : Access)
 (num_elem_per_idx : Immediate := .int 1)
 (num_valid_indices : Option Immediate := none)
 -- kwargs
 (mask: Option Immediate := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .localGather {
      dst := .abstract dst,
      src := .abstract src_buffer,
      index := .abstract index,
      numElemPerIdx := num_elem_per_idx,
      numValidIndicies := num_valid_indices,
    }
    return .none

nki dma_copy
 -- kwargs
 (dst : Access)
 (src : Access)
 (mask: Option Immediate := none)
 (dst_rmw_op : Option AluOp := none)
 (mode : Nat := 0)
 (dge_mode : Nat := 0) := do
  if mask.isSome then throw maskNotSupported
  let op : DgeComputeOp := <- match dst_rmw_op with
    | none => .ok .none
    | some rmw_op => match rmw_op with
      | .add => .ok .add
      | _ => throw "Unsupported operation"
  if mode > 1 then throw "unsupported oob mode"
  Trace.add_stmt $ .oper $ .dmaCopy {
      dst := .abstract dst,
      src := .abstract src,
      compute_op := op,
      oobMode := match mode with
        | 0 => .enable
        | 1 => .disable
        | _ => .disable,
      dgeMode := dge_mode,
  }
  return .none

nki max8
 (dst: Access)
 -- kwargs
 (src : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .max8  {
        dst := .abstract dst,
        src := .abstract src,
        dtype := dtype
    }
    return .none

nki nc_find_index8
 (dst: Access)
 -- kwargs
 (data : Access)
 (vals : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    -- TODO assert that vals is a tensor containing the 8 values per partition
    Trace.add_stmt $ .oper $ .findIndex8 {
      dst := .abstract dst,
      src := .abstract data,
      vals := .abstract vals,
      dtype := dtype
    }
    return .none

nki nc_match_replace8
 (dst: Access)
 -- kwargs
 (data : Access)
 (vals : Access)
 (imm : Immediate)
 (dst_idx : Option Access := none)
 (mask: Option Immediate := none)
 (dtype: Option Dtype := none) := do
    if mask.isSome then throw maskNotSupported
    -- TODO assert that vals is a tensor containing the 8 values per partition
    Trace.add_stmt $ .oper $ .matchReplace8 {
      dst           := .abstract dst,
      src           := .abstract data,
      vals          := .abstract vals,
      replaceValue  := imm,
      dstIdx        := dst_idx.map .abstract
      dtype         := dtype
    }
    return .none


nki nc_stream_shuffle
 (src : Access)
 (dst : Access)
 (shuffle_mask : List Immediate)
 -- kwargs
 (dtype: Option Dtype := none)
 (mask: Option Immediate := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper $ .shuffle {
      dst := .abstract dst,
      src := .abstract src,
      shuffleMask := shuffle_mask,
      dtype := dtype,
    }
    return .none
