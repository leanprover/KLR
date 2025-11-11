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

namespace KLR.Trace.Isa
open KLR.Core

private def maskNotSupported := "mask parameter is not supported"

def converRevOps (reverse0 : Bool) (reverse1 : Bool) : TensorScalarReverseOps :=
  match reverse0, reverse1 with
    | false, false => .none
    | true, false => .first
    | false, true => .second
    | true, true => .both

def dimsFromPythonDefs (d : Sum Int (List Int)) : Trace TensorSubDim :=
  match d with
  | .inl 1 => return .X
  | .inl _ => throw  "not a valid dim"
  | .inr r => match r with
    | [4] => return .X
    | [3, 4] => return .XY
    | [2, 3, 4] => return .XYZ
    | [1, 2, 3, 4] => return .XYZW
    | _ => throw "not a valid dim"

def getTransposeOps(op: Option (List Int)) : Trace TransposeOps :=
  match op with
  | none => return .None -- WZYX
  | some [0, 1, 2, 3] => return .None -- WZYX (identity)
  | some [0, 1, 3, 2] => return .WZXY
  | some [0, 3, 1, 2] => return .WXZY
  | some [0, 2, 3, 1] => return .WYXZ
  | some [1, 0, 2, 3] => return .ZWYX
  | some [1, 2, 0, 3] => return .ZYWX
  | some [1, 2, 3, 0] => return .ZYXW
  | some [2, 3, 0, 1] => return .YXWZ
  | some [2, 3, 1, 0] => return .YXZW
  | some [2, 0, 1, 3] => return .YWZX
  | some [3, 0, 1, 2] => return .XWZY
  | some [3, 1, 2, 0] => return .XZYW
  | some [3, 2, 1, 0] => return .XYZW
  | some [3, 2, 0, 1] => return .XYWZ
  | some _ => throw "unsupported transpose operation"

nki builtin.isa.get_nc_version := do
  lookup `arch

---- Register APIs

private def getReg : Term -> Trace Name
  | .scalar s => return s
  | _ => throw "expecting register value"

nki builtin.isa.register_alloc (t : Option Int := none) := do
  let reg <- genName `reg
  add_stmt (.oper (.registerMove {
    dst := reg.toString
    imm := t.getD 0
    })
    (<- genName `move).toString
  )
  return .scalar reg

nki builtin.isa.register_move (dst : Term) (imm : Int) := do
  let reg <- getReg dst
  add_stmt (.oper (.registerMove {
    dst := reg.toString
    imm := imm
    })
    (<- genName `move).toString
  )
  return .scalar reg

nki builtin.isa.register_load (dst : Term) (src : Access) := do
  let reg <- getReg dst
  add_stmt (.oper (.tensorLoad {
    dst := reg.toString
    src := .abstract src
    })
    (<- genName `load).toString
  )
  return .scalar reg

nki builtin.isa.register_store (dst : Access) (src : Term) := do
  let reg <- getReg src
  add_stmt (.oper (.tensorStore {
    dst := .abstract dst
    src := reg.toString
    })
    (<- genName `store).toString
  )
  return .scalar reg

---- ISA APIs

nki builtin.isa.nc_matmul
 (dst : Access)
 (stationary : Access)
 (moving : Access)
 -- kwargs
 (is_stationary_onezero : Bool := false)
 (is_moving_zero : Bool := false)
 (is_transpose : Bool := false)
 (tile_position : List Nat := [])
 (tile_size : List Nat := [])
 (psumAccumulateFlag : Nat := 3) -- assume the whole tensor
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
      psumAccumulateFlag := psumAccumulateFlag
      }) name
    return .none

nki builtin.isa.nc_transpose
 (dst : Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
  if mask.isSome then
    throw maskNotSupported
  match engine with
  | .pe =>
    let N := data.shapePure.freeDims.getLast!
    let id : TensorRef := <- match <- lookup_global? (.num `identity 0) with
    | some (.access acc) => return .abstract acc
    | some _ => throw "identity has wrong type"
    | none => throw "identity not defined"
    let idName : TensorName <- match id with
    | .abstract $ .simple t => pure t
    | .abstract $ .basic t => pure  t.tensor
    | .abstract $ .pattern t => pure t.tensor
    | _ => throw "Expected identity matrix to be a ref"
    let idSlice : TensorRef := .abstract $ .basic $ <- AccessBasic.make idName [
        .slice $ Slice.make! 0 N 1,
        .slice $ Slice.make! 0 N 1
      ]
    Trace.add_stmt $ .oper (.ncMatMul {
      dst := .abstract dst,
      stationary := idSlice,
      moving := .abstract data,
      isStationaryOneZero := false,
      isMovingZero := false,
      isTranspose := true,
      tilePosition := [],
      tileSize := [],
      psumAccumulateFlag := 3 -- assume whole tensor
    }) name
  | _ =>
    Trace.add_stmt $ .oper (.transpose {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dst.tensor.dtype,
      engine := engine,
    }) name
  return .none

nki builtin.isa.activation
 (dst : Access)
 (op : ActivationFunc)
 (data : Access)
 -- kwargs
 (bias : Option Access := none)
 (scale : Sum Immediate Access := .inl $ .float 1.0) -- This also can accept a tensor
 (reduce_op : Option AluOp := none)
 (reduce_res : Option Access := none)
 (reduce_cmd : AccumCmd := .Idle)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
  if mask.isSome then
    throw maskNotSupported
  Trace.add_stmt $ .oper (.ncActivate {
    dst := .abstract dst,
    src := .abstract data,
    accumulatorCmd := reduce_cmd,
    activationFunc := op,
    scale := match scale with
    | .inl imm => .imm imm
    | .inr t => .tile $ .abstract t,
    bias := bias.map .abstract,
    reduceOp := reduce_op,
    reduceRes := reduce_res.map .abstract,
    dtype := dst.tensor.dtype,
  }) name
  return .none

nki builtin.isa.activation_reduce
 (dst: Access)
 (op : ActivationFunc)
 (data : Access)
 -- kwargs
 (reduce_op : Option AluOp := none)
 (reduce_res : Option Access := none)
 (bias : Option Access := none )
 (scale : Sum Immediate Access := .inl $ .float 1.0)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    if scale.isRight then
      throw "scale can't be specified as tensor"
    Trace.add_stmt $ .oper (.activationReduce {
      dst := .abstract dst,
      activationFunc := op,
      src := .abstract data,
      scale := match scale with
      | .inl imm => .imm imm
      | .inr t => .tile $ .abstract t,
      bias := bias.map .abstract,
      reduceOp := reduce_op,
      reduceRes := reduce_res.map .abstract,
      accumulatorCmd := .ZeroAccumulate,
      dtype := dst.tensor.dtype,
    }) name
    return .none

nki builtin.isa.tensor_reduce
  (dst: Access)
  (op : AluOp)
  (data : Access)
  (axis : Sum Int (List Int))
  -- kwargs
  (mask : Option Immediate := none)
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
      dtype := dst.tensor.dtype,
      negated := negate,
      keepdims := keepdims
    }) name
    return .none

nki builtin.isa.tensor_partition_reduce
  (dst: Access)
  (op : AluOp)
  (data : Access)
  -- kwargs
  (mask : Option Immediate := none)
  (name : Option String := none) := do
    if mask.isSome then
      throw maskNotSupported
    Trace.add_stmt $ .oper (.tensorPartitionReduce {
      dst := .abstract dst,
      op := op,
      data := .abstract data,
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.tensor_tensor
 (dst: Access)
 (data1 : Access)
 (data2 : Access)
 (op : AluOp)
 -- kwargs
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
      dtype := dst.tensor.dtype,
      engine := engine
    }) name
    return .none

nki builtin.isa.tensor_tensor_scan
 (dst: Access)
 (data0 : Access)
 (data1 : Access)
 (initial : Sum Immediate Access)
 (op0 : AluOp)
 (op1 : AluOp)
 (reverse0 : Bool := false)
 (reverse1 : Bool := false)
 -- kwargs
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
        dtype := dst.tensor.dtype
        accumulatorCmd := .Idle
    }) name
    return .none

nki builtin.isa.scalar_tensor_tensor
 (dst : Access)
 -- kwargs
 (data : Access)
 (op0 : AluOp)
 (operand0 : Sum Immediate Access)
 (op1 : AluOp)
 (operand1 : Sum Immediate Access)
 (reverse0 : Bool := false)
 (reverse1 : Bool := false)
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
        dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.tensor_scalar
 (dst: Access)
 (data : Access)
 (op0 : AluOp)
 (operand0 : Sum Immediate Access)
 (reverse0 : Bool := false)
 (op1 : Option AluOp := none)
 (operand1 : Option (Sum Immediate Access) := none)
 (reverse1 : Bool := false)
 -- kwargs
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
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.tensor_scalar_reduce
 (dst : Access)
 -- kwargs
 (data : Access)
 (op0 : AluOp)
 (operand0 : Sum Immediate Access)
 (reduce_op : AluOp)
 (reduce_res : Access)
 (reverse0 : Bool := false)
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
        dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.tensor_copy
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

nki builtin.isa.tensor_copy_dynamic_src
 -- kwargs
 (dst : Access)
 (src : Access)
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncCopy {
      dst := .abstract dst
      src := .abstract src
      dtype := dst.tensor.dtype
      engine := engine
    }) name
    return .none

nki builtin.isa.tensor_copy_dynamic_dst
 (dst : Access)
 (src : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.ncCopy {
      dst := .abstract dst
      src := .abstract src
      dtype := dst.tensor.dtype
      engine := engine
    }) name
    return .none

nki builtin.isa.tensor_copy_predicated
 -- kwargs
 (dst : Access)
 (src : Access)
 (predicate : Access)
 (mask : Option Immediate := none)
 (reverse_pred : Bool := false)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.copyPredicated  {
      dst := .abstract dst,
      src := .abstract src,
      predicate := .abstract predicate,
      dtype := dst.tensor.dtype,
      reversePred := reverse_pred,
    }) name
    return .none

nki builtin.isa.reciprocal
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.reciprocal {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.iota
 (dst: Access)
 (pattern : List (Int × Nat))
 (offset : Int := 0)
 (channel_multiplier : Int := 0)
 -- kwargs
 (name : Option String := none) := do
    let pairs := pattern.map fun (i, n) => APPair.mk i n 0
    Trace.add_stmt $ .oper (.iota {
      dst := .abstract dst,
      pattern := ⟨ offset, pairs, channel_multiplier ⟩
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.dropout
 (dst: Access)
 (data : Access)
 (prob : Sum Immediate Access)
 -- kwargs
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.dropout {
        dst       := .abstract dst,
        src       := .abstract data,
        threshold := match prob with
          | .inl i => .imm i
          | .inr t => .tile $ .abstract t
        thresholdType := .KeepRate
        dtype         := dst.tensor.dtype,
    }) name
    return .none

nki builtin.isa.affine_select
 (dst: Access)
 (pattern : List (Int × Nat))
 (offset : Int := 0)
 (channel_multiplier : Int := 0)
 (on_true_tile : Access)
 (on_false_value : Immediate)
 -- kwargs
 (cmp_op : AluOp := .is_equal)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    let pairs := pattern.map fun (i, n) => APPair.mk i n 0
    Trace.add_stmt $ .oper (.ncAffineSelect {
      dst := .abstract dst,
      pred := ⟨offset, pairs, channel_multiplier⟩ ,
      onTrueTile := .abstract on_true_tile,
      onFalseValue := on_false_value,
      dtype := dst.tensor.dtype,
      cmpOp := cmp_op,
    }) name
    return .none

nki builtin.isa.range_select
 (dst: Access)
 -- kwargs
 (on_true_tile : Access)
 (comp_op0 : AluOp)
 (comp_op1 : AluOp)
 (bound0 : Access)
 (bound1 : Access)
 (reduce_cmd : AccumCmd := AccumCmd.Idle)
 (reduce_res : Option Access := none)
 (reduce_op : Option AluOp := some .max)
 (range_start : Immediate := .float 0.0)
 (on_false_value : Immediate := .float (-1.0 / 0.0))
 (mask : Option Immediate := none)
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
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.memset
 (dst: Access)
 (value : Immediate)
 -- kwargs
 (mask : Option Immediate := none)
 (engine : Engine := Engine.unassigned)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.memSet {
      dst    := .abstract dst,
      value  := value,
      dtype  := dst.tensor.dtype,
      engine := engine
    }) name
    return .none

nki builtin.isa.bn_stats
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask: Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.batchNormStats {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.bn_aggr
 (dst: Access)
 (data : Access)
 -- kwargs
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.batchNormAggregate {
      dst := .abstract dst,
      src := .abstract data,
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.local_gather
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

nki builtin.isa.dma_copy
 (dst : Access)
 (src : Access)
 -- kwargs
 (mask: Option Immediate := none)
 (dst_rmw_op : Option AluOp := none)
 (oob_mode : Nat := 0)
 (dge_mode : Nat := 0)
 (name : Option String := none) := do
  if mask.isSome then throw maskNotSupported
  let op : DgeComputeOp := <- match dst_rmw_op with
    | none => return .none
    | some rmw_op => match rmw_op with
      | .add => return .add
      | _ => throw "Unsupported operation"
  if oob_mode > 1 then throw "unsupported oob mode"
  Trace.add_stmt $ .oper (.ncDmaCopy {
      dst := .abstract dst,
      src := .abstract src,
      compute_op := op,
      oobMode := match oob_mode with
        | 0 => .error
        | 1 => .skip
        | _ => .skip,
      dgeMode := dge_mode,
  }) name
  return .none

nki builtin.isa.dma_transpose
  (dst : Access)
  (src : Access)
  -- kwargs
  (axes : Option (List Int) := none)
  (mask : Option Immediate := none)
  (dge_mode : Nat := 0)
  (name : Option String := none) := do
  if mask.isSome then throw maskNotSupported
  if src.shapePure.toList.length != 4 then
    throw "source tensor must have 4 dimmensions"
  if dst.shapePure.toList.length != 4 then
    throw "destination tensor must have 4 dimmensions"
  Trace.add_stmt $ .oper (.dmaTranspose {
    dst := .abstract dst,
    src := .abstract src,
    axes := <- getTransposeOps axes,
    dtype := dst.tensor.dtype
    dgeMode := dge_mode
  }) name
  return .none

nki builtin.isa.max8
 (dst: Access)
 -- kwargs
 (src : Access)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.max8  {
        dst := .abstract dst,
        src := .abstract src,
        dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.nc_find_index8
 (dst: Access)
 -- kwargs
 (data : Access)
 (vals : Access)
 (mask : Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    -- TODO assert that vals is a tensor containing the 8 values per partition
    Trace.add_stmt $ .oper (.findIndex8 {
      dst := .abstract dst,
      src := .abstract data,
      vals := .abstract vals,
      dtype := dst.tensor.dtype
    }) name
    return .none

nki builtin.isa.nc_match_replace8
 (dst: Access)
 -- kwargs
 (data : Access)
 (vals : Access)
 (imm : Immediate)
 (dst_idx : Option Access := none)
 (mask: Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    -- TODO assert that vals is a tensor containing the 8 values per partition
    Trace.add_stmt $ .oper (.matchReplace8 {
      dst           := .abstract dst,
      src           := .abstract data,
      vals          := .abstract vals,
      replaceValue  := imm,
      dstIdx        := dst_idx.map .abstract
      dtype         := dst.tensor.dtype
    }) name
    return .none


nki builtin.isa.nc_stream_shuffle
 (dst : Access)
 (src : Access)
 (shuffle_mask : List Immediate)
 -- kwargs
 (mask: Option Immediate := none)
 (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.shuffle {
      dst := .abstract dst,
      src := .abstract src,
      shuffleMask := shuffle_mask,
      dtype := dst.tensor.dtype,
    }) name
    return .none

nki builtin.isa.select_reduce
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
      dtype := dst.tensor.dtype,
    }) name
    return .none

nki builtin.isa.sequence_bounds
  (dst : Access)
  -- kwargs
  (segment_ids : Access)
  (dtype : Option Dtype := none)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.sequenceBounds {
      dst := .abstract dst,
      segmentIds := .abstract segment_ids,
      dtype := dtype
    }) name
    return .none

nki builtin.isa.sendrecv
  (src: Access)
  (dst: Access)
  (send_to_rank: Immediate)
  (recv_from_rank: Immediate)
  (pipe_id: Int)
  (mask : Option Immediate := none)
  (use_gpsimd_dma: Bool := false)
  (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.sendRecv {
      dst := .abstract dst,
      src := .abstract src,
      sendToRank := send_to_rank,
      recvFromRank := recv_from_rank,
      pipeId := .int pipe_id,
      useGpsimdDma := use_gpsimd_dma
    }) name
    return .none

nki builtin.isa.sendrecv_cce
  (src: List Access)
  (dst: Access)
  (send_to_rank: Immediate)
  (recv_from_ranks: List Immediate)
  (pipe_id: Int)
  (op : AluOp)
  (mask : Option Immediate := none)
  (name : Option String := none) := do
    if mask.isSome then throw maskNotSupported
    Trace.add_stmt $ .oper (.sendRecvCCE {
      dst := .abstract dst,
      src := <- src.mapM (fun x => return .abstract x),
      sendToRank := send_to_rank,
      recvFromRanks := recv_from_ranks,
      pipeId := .int pipe_id,
      op := op
    }) name
    return .none

nki builtin.isa.quantize_mx
  (dst : Access)
  (src: Access)
  (dst_scale : Access)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.quantizeMX {
      dst := .abstract dst,
      src := .abstract src,
      dstScale := .abstract dst_scale,
    }) name
    return .none

nki builtin.isa.nc_matmul_mx
  (dst : Access)
  (stationary: Access)
  (moving: Access)
  (stationary_scale: Access)
  (moving_scale: Access)
  (tile_position : Option (List Nat) := none)
  (tile_size : Option (List Nat) := none)
  (psumAccumulateFlag : Nat := 3) -- assume whole tensor
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.ncMatMulMX {
        dst := .abstract dst
        stationary := .abstract stationary
        moving := .abstract moving
        stationaryScale := .abstract stationary_scale
        movingScale := .abstract moving_scale
        psumAccumulateFlag := psumAccumulateFlag,
        tilePosition := tile_position,
        tileSize :=  tile_size,
      }) name
    return .none

nki builtin.isa.dma_compute
  (dst : Access)
  (srcs : List Access)
  (scales : List Immediate)
  (reduce_op : AluOp)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.dmaCompute {
      dst := .abstract dst,
      srcs := srcs.map .abstract,
      scales := scales,
      reduceOp := reduce_op,
    }) name
    return .none

nki builtin.isa.all_reduce
  (op : AluOp)
  (srcs : List Access)
  (dsts : List Access)
  (replica_groups: List (List Int))
  (name : Option String := none) := do
    Trace.add_stmt $ .oper ( .allReduce {
      dsts := dsts.map .abstract
      srcs := srcs.map .abstract
      op := some op
      replicaGroups := some replica_groups
      reduceScatterDim := none
      allGatherDim := none
      sourceTargetPairs := none
      broacastSizes := none
      splitDim := none
      concatDim := none
    }) name
    return .none


nki builtin.isa.all_gather
  (op : AluOp)
  (srcs : List Access)
  (dsts : List Access)
  (replica_groups : List (List Int))
  (all_gather_dim : Int)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.allGather {
      dsts := dsts.map .abstract
      srcs := srcs.map .abstract
      op := some op
      replicaGroups := some replica_groups
      allGatherDim := some all_gather_dim
      reduceScatterDim := none
      sourceTargetPairs := none
      broacastSizes := none
      splitDim := none
      concatDim := none
    }) name
    return .none


nki builtin.isa.reduce_scatter
  (op : AluOp)
  (srcs : List Access)
  (dsts : List Access)
  (replica_groups : List (List Int))
  (reduce_scatter_dim : Int)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.reduceScatter {
      dsts := dsts.map .abstract
      srcs := srcs.map .abstract
      op := some op
      replicaGroups := some replica_groups
      reduceScatterDim := some reduce_scatter_dim
      allGatherDim := none
      sourceTargetPairs := none
      broacastSizes := none
      splitDim := none
      concatDim := none
    }) name
    return .none


nki builtin.isa.collective_permute
  (srcs : List Access)
  (dsts : List Access)
  (source_target_pairs: List (List Int))
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.collectivePermute {
      dsts := dsts.map .abstract
      srcs := srcs.map .abstract
      op := none
      replicaGroups := none
      sourceTargetPairs := some source_target_pairs
      reduceScatterDim := none
      allGatherDim := none
      broacastSizes := none
      splitDim := none
      concatDim := none
    }) name
    return .none

nki builtin.isa.broadcast
  (op : AluOp)
  (srcs : List Access)
  (dsts : List Access)
  (replica_groups : List (List Int))
  (broadcast_sizes : List Int)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.broadcast {
      dsts := dsts.map .abstract
      srcs := srcs.map .abstract
      op := some op
      replicaGroups := some replica_groups
      reduceScatterDim := none
      allGatherDim := none
      sourceTargetPairs := none
      broacastSizes := some broadcast_sizes
      splitDim := none
      concatDim := none
    }) name
    return .none

nki builtin.isa.all_to_all
  (op : AluOp)
  (srcs : List Access)
  (dsts : List Access)
  (replica_groups : List (List Int))
  (split_dimension : Int)
  (concat_dimension : Int)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.allToAll {
      dsts := dsts.map .abstract
      srcs := srcs.map .abstract
      op := some op
      replicaGroups := some replica_groups
      reduceScatterDim := none
      allGatherDim := none
      sourceTargetPairs := none
      broacastSizes := none
      splitDim := some split_dimension
      concatDim := some concat_dimension
    }) name
    return .none

nki builtin.isa.send
  (op : AluOp)
  (srcs : List Access)
  (peerId : Int)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.send {
      op := op,
      srcs := srcs.map .abstract
      peerId := peerId
    }) name
    return .none

nki builtin.isa.recv
  (op : AluOp)
  (dsts : List Access)
  (replica_groups : List Int)
  (peer_id : Int)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.recv {
      op := op,
      dsts := dsts.map .abstract
      replicaGroups := replica_groups
      peerId := peer_id
    }) name
    return .none

nki builtin.isa.core_barrier
  (data : Access)
  (cores : List Int)
  (engine : Engine := .unassigned)
  (name : Option String := none) := do
    Trace.add_stmt $ .oper (.coreBarrier {
      data := .abstract data,
      cores := cores,
      engine := engine
    }) name
    return .none
