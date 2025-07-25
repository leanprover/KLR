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

def dimsFromPythonDefs(d : Sum Int (List Int)) : Trace TensorSubDim :=
  match d with
  | .inl 1 => .ok .X
  | .inl _ => throw  "not a valid dim"
  | .inr r => match r with
    | [1] => .ok .X
    | [1, 2] => .ok .XY
    | [1, 2, 3] => .ok .XYZ
    | [1, 2, 3, 4] => .ok .XYZW
    | _ => throw "not a valid dim"

def getTransposeOps(op: Option (List Int)) : Trace TransposeOps :=
  match op with
  | none => .ok .None -- WZYX
  | some [0, 1, 2, 3] => .ok .None -- WZYX (identity)
  | some [0, 1, 3, 2] => .ok .WZXY
  | some [0, 3, 1, 2] => .ok .WXZY
  | some [0, 2, 3, 1] => .ok .WYXZ
  | some [1, 0, 2, 3] => .ok .ZWYX
  | some [1, 2, 0, 3] => .ok .ZYWX
  | some [1, 2, 3, 0] => .ok .ZYXW
  | some [2, 3, 0, 1] => .ok .YXWZ
  | some [2, 3, 1, 0] => .ok .YXZW
  | some [2, 0, 1, 3] => .ok .YWZX
  | some [3, 0, 1, 2] => .ok .XWZY
  | some [3, 1, 2, 0] => .ok .XZYW
  | some [3, 2, 1, 0] => .ok .XYZW
  | some [3, 2, 0, 1] => .ok .XYWZ
  | some _ => throw "unsupported transpose operation"


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
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper (.ncMatMul {
      dst := .abstract dst,
      stationary := .abstract stationary,
      moving := .abstract moving,
      isStationaryOneZero := is_stationary_onezero,
      isMovingZero := is_moving_zero,
      isTranspose := is_transpose,
      tilePosition := tile_position,
      tileSize := tile_size,
      }) name
    return .none

nki nc_transpose
 (dst : Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
  if mask.isSome then
    throw maskNotSupported
  Trace.add_stmt $ .oper (.transpose {
    dst := .abstract dst,
    src := .abstract data,
    dtype := dtype,
    engine := engine,
  }) name
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
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
  if mask.isSome then
    throw maskNotSupported
  Trace.add_stmt $ .oper (.ncActivate {
    dst := .abstract dst,
    src := .abstract data,
    accumulatorCmd := reduce_cmd,
    activationFunc := op,
    scale := scale,
    bias := bias,
    reduceOp := reduce_op,
    reduceRes := reduce_res.map .abstract,
    dtype := dtype,
  }) name
  return .none

nki activation_reduce
 (dst: Access)
 (op : ActivationFunc)
 (data : Access)
 -- kwargs
 (reduce_op : Option AluOp := none)
 (reduce_res : Option Access := none)
 (reduce_cmd : AccumCmd := .Idle)
 (bias : Immediate := .float 0)
 (scale : Sum Immediate Access := .inl (.float 1.0))
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    if scale.isRight then
      throw "scale can't be specified as tensor"
    Trace.add_stmt $ .oper (.activationReduce {
      dst := .abstract dst,
      activationFunc := op,
      src := .abstract data,
      bias := bias,
      reduceOp := reduce_op,
      reduceRes := reduce_res.map .abstract,
      accumulatorCmd := reduce_cmd,
      scale := <- scale.getLeft?,
      dtype := dtype,
    }) name
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
  (keepdims : Bool := false)
  (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper (.tensorReduce {
      dst  := .abstract dst,
      src  := .abstract data,
      op   := op,
      opDim := <- dimsFromPythonDefs axis,
      dtype := dtype,
      negated := negate,
      keepdims := keepdims
    }) name
    return .none

nki tensor_partition_reduce
  (dst: Access)
  (op : AluOp)
  (data : Access)
  -- kwargs
  (mask : Option Immediate := none)
  (dtype : Option Dtype := none)
  (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper (.tensorPartitionReduce {
      dst := .abstract dst,
      op := op,
      data := .abstract data
      dtype := dtype
    }) name
    return .none

nki tensor_tensor
 (dst: Access)
 (data1 : Access)
 (data2 : Access)
 (op : AluOp)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper (.tensorTensor {
      dst := .abstract dst,
      src0 := .abstract data1,
      src1 := .abstract data2,
      op := op,
      dtype := dtype,
      engine := engine
    }) name
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
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1
    Trace.add_stmt $ .oper (.tensorTensorScan {
        dst := .abstract dst
        src0 := .abstract data0
        src1 := .abstract data1
        op0 := op0
        op1 := op1
        reverseOperands := rev
        imm0 := match initial with
          | .inl l => .imm l
          | .inr t => .tile $ .abstract t,
        dtype := dtype
        accumulatorCmd := .Idle
    }) name
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
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1
    Trace.add_stmt $ .oper (.ncScalarTensorTensor {
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
    }) name
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
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1
    Trace.add_stmt $ .oper (.tensorScalar {
      dst := .abstract dst,
      src := .abstract data
      imm0 := match operand0 with
        | .inl i => .imm i
        | .inr t => .tile $ .abstract t
      op0 := op0
      imm1 := match operand1 with
        | some (.inl i) => some $ .imm i
        | some (.inr t) => some $ .tile $ .abstract t
        | none => none
      op1 := op1
      reverse := rev
      engine := engine
      dtype := dtype
    }) name
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
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.tensorScalarReduce {
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
    }) name
    return .none

nki tensor_copy
 (dst: Access)
 (src : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncCopy {
      dst := .abstract dst
      src := .abstract src
      dtype := dtype
      engine := engine
    }) name
    return .none

nki tensor_copy_dynamic_src
 (dst : Access)
 (src : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncCopy {
      dst := .abstract dst
      src := .abstract src
      dtype := dtype
      engine := engine
    }) name
    return .none

nki tensor_copy_dynamic_dst
 (dst : Access)
 (src : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncCopy {
      dst := .abstract dst
      src := .abstract src
      dtype := dtype
      engine := engine
    }) name
    return .none

nki tensor_copy_predicated
 (dst : Access)
 -- kwargs
 (src : Access)
 (predicate : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (reverse_pred : Bool := false)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.copyPredicated  {
      dst := .abstract dst,
      src := .abstract src,
      predicate := .abstract predicate,
      dtype := dtype,
      reversePred := reverse_pred,
    }) name
    return .none

nki reciprocal
 (dst: Access)
 (data : Access)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.reciprocal {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dtype
    }) name
    return .none

nki iota
 (dst: Access)
 (_expr : Int)
 -- kwargs
 (dtype : Option Dtype := none)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.iota {
      dst := .abstract dst,
      pattern := ⟨ 0, []⟩
      dtype := dtype
    }) name
    return .none

nki dropout
 (dst: Access)
 (data : Access)
 (prob : Sum Immediate Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.dropout {
        dst       := .abstract dst,
        src       := .abstract data,
        threshold := match prob with
          | .inl i => .imm i
          | .inr t => .tile $ .abstract t
        thresholdType := .KeepRate
        dtype         := dtype,
    }) name
    return .none

nki affine_select
 (dst: Access)
 (_pred : Int)
 (on_true_tile : Access)
 (on_false_value : Immediate)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncAffineSelect {
      dst := .abstract dst,
      pred := ⟨ 0, [] ⟩,
      onTrueTile := .abstract on_true_tile,
      onFalseValue := on_false_value,
      dtype := dtype,
      cmpOp := .is_equal,
    }) name
    return .none

nki range_select
 (dst: Access)
 (on_true_tile : Access)
 (comp_op0 : AluOp)
 (comp_op1 : AluOp)
 (bound0 : Access)
 (bound1 : Access)
 -- kwargs
 (reduce_cmd : AccumCmd := AccumCmd.Idle)
 (reduce_res : Option Access := none)
 (reduce_op : Option AluOp := some .max)
 (range_start : Immediate := .float 0)
 (on_false_value : Immediate := .float 0)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncRangeSelect {
      dst := .abstract dst,
      reduceCommand := reduce_cmd,
      reduceRes := reduce_res.map .abstract
      reduceOp := reduce_op
      compOp0 := comp_op0,
      compOp1 := comp_op1,
      bound0 := .abstract bound0,
      bound1 := .abstract bound1,
      rangeStart := range_start,
      onTrueTile := .abstract on_true_tile,
      onFalseValue := on_false_value,
      dtype := dtype
    }) name
    return .none

nki memset
 (dst: Access)
 (value : Immediate)
 (dtype : Dtype)
 -- kwargs
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.memSet {
      dst    := .abstract dst,
      value  := value,
      dtype  := dtype,
      engine := engine
    }) name
    return .none

nki bn_stats
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask: Option Immediate := none)
 (dtype: Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.batchNormStats {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dtype
    }) name
    return .none

nki bn_aggr
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.batchNormAggregate {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dtype
    }) name
    return .none

nki local_gather
 (dst: Access)
 (src_buffer : Access)
 (index : Access)
 (num_elem_per_idx : Immediate := .int 1)
 (num_valid_indices : Option Immediate := none)
 -- kwargs
 (mask: Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncLocalGather {
      dst := .abstract dst,
      src := .abstract src_buffer,
      index := .abstract index,
      numElemPerIdx := num_elem_per_idx,
      numValidIndicies := num_valid_indices,
    }) name
    return .none

nki dma_copy
 (dst : Access)
 (src : Access)
 -- kwargs
 (mask: Option Immediate := none)
 (dst_rmw_op : Option AluOp := none)
 (mode : Nat := 0)
 (dge_mode : Nat := 0)
 (name : Option String := none) := do
  if mask.isSome then throw maskNotSupported
  let op : DgeComputeOp := <- match dst_rmw_op with
    | none => .ok .none
    | some rmw_op => match rmw_op with
      | .add => .ok .add
      | _ => throw "Unsupported operation"
  if mode > 1 then throw "unsupported oob mode"
  Trace.add_stmt $ .oper (.ncDmaCopy {
      dst := .abstract dst,
      src := .abstract src,
      compute_op := op,
      oobMode := match mode with
        | 0 => .enable
        | 1 => .disable
        | _ => .disable,
      dgeMode := dge_mode,
  }) name
  return .none

nki dma_transpose
  (dst : Access)
  (src : Access)
  -- kwargs
  (axes : Option (List Int) := none)
  (mask : Option Immediate := none)
  (dtype : Option Dtype := none)
  (name : Option String := none) := do
  if mask.isSome then throw maskNotSupported
  Trace.add_stmt $ .oper (.dmaTranspose {
    dst := .abstract dst,
    src := .abstract src,
    axes := <- getTransposeOps axes,
    dtype := dtype
  }) name
  return .none

nki max8
 (dst: Access)
 -- kwargs
 (src : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.max8  {
        dst := .abstract dst,
        src := .abstract src,
        dtype := dtype
    }) name
    return .none

nki nc_find_index8
 (dst: Access)
 -- kwargs
 (data : Access)
 (vals : Access)
 (mask : Option Immediate := none)
 (dtype : Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    -- TODO assert that vals is a tensor containing the 8 values per partition
    Trace.add_stmt $ .oper (.findIndex8 {
      dst := .abstract dst,
      src := .abstract data,
      vals := .abstract vals,
      dtype := dtype
    }) name
    return .none

nki nc_match_replace8
 (dst: Access)
 -- kwargs
 (data : Access)
 (vals : Access)
 (imm : Immediate)
 (dst_idx : Option Access := none)
 (mask: Option Immediate := none)
 (dtype: Option Dtype := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    -- TODO assert that vals is a tensor containing the 8 values per partition
    Trace.add_stmt $ .oper (.matchReplace8 {
      dst           := .abstract dst,
      src           := .abstract data,
      vals          := .abstract vals,
      replaceValue  := imm,
      dstIdx        := dst_idx.map .abstract
      dtype         := dtype
    }) name
    return .none


nki nc_stream_shuffle
 (src : Access)
 (dst : Access)
 (shuffle_mask : List Immediate)
 -- kwargs
 (dtype: Option Dtype := none)
 (mask: Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.shuffle {
      dst := .abstract dst,
      src := .abstract src,
      shuffleMask := shuffle_mask,
      dtype := dtype,
    }) name
    return .none

nki select_reduce
  (dst : Access)
  (predicate : Access)
  (on_true : Access)
  (on_false : Sum Immediate Access)
  -- kwargs
  (reduce_res : Option Access := none)
  (reduce_cmd: AccumCmd := .Idle)
  (reduce_op : AluOp := .max)
  (reverse_pred : Bool := false)
  (mask : Option Immediate := none)
  (dtype : Option Dtype := none)
  (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.selectReduce {
      dst := .abstract dst,
      predicate := .abstract predicate,
      onTrue := .abstract on_true,
      onFalse := match on_false with
        | .inl imm => .imm imm
        | .inr tensor => .tile $ .abstract tensor,
      reduceRes := reduce_res.map .abstract,
      reduceCmd := reduce_cmd,
      reduceOp := reduce_op,
      reversePred := reverse_pred,
      dtype := dtype,
    }) name
    return .none

nki sequence_bounds
  (dst : Access)
  (segment_ids : Access)
  -- kwargs
  (dtype : Option Dtype := none)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.sequenceBounds {
      dst := .abstract dst,
      segmentIds := .abstract segment_ids,
      dtype := dtype
    }) name
    return .none
