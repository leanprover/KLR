/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Potapov
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Tensor

namespace KLR.KLR.Trace
open KLR.Core

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
 (dst : TensorSram)
 (stationary : TensorSram)
 -- kwargs
 (moving : TensorSram)
 (_is_stationary_onezero : Bool := false) -- FIXME good to have
 (_is_moving_zero : Bool := false) -- FiXME good to have
 (is_transpose : Bool := false)
 (_tile_position : Shape := <-  Shape.fromList []) -- FIXME
 (_tile_size : Shape := <- Shape.fromList []) -- FIXME
 (_mask : Option Immediate := none) := do
    -- got to emit load statioary before
    -- accumulated flag is not supported yet
    let dstT : TensorRef := .abstract $ .simple dst
    let movingT : TensorRef := .abstract $ .simple moving
    let stationaryT : TensorRef := .abstract $ .simple stationary
    let accFlag : MatmulGroupElement := .whole -- TODO: need to figure out which one it is
    let ls : LoadStationary := ⟨ stationaryT, is_transpose ⟩
    let mm : MatMul := ⟨ dstT, movingT, accFlag ⟩
    return .oper [(.LoadStationary ls), (.MatMul mm)]

nki nc_transpose
 (dst : TensorSram)
 (data : TensorSram)
 -- kwargs
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none)
 (_engine : Engine := Engine.unassigned) := do
  let dstT : TensorRef := .abstract $ .simple dst
  let srcT : TensorRef := .abstract $ .simple data
  let trn : Transpose := ⟨ dstT, srcT ⟩
  return .oper [.Transpose trn]

nki activation
 (dst : TensorSram)
 (op : ActivationFunc)
 (data : TensorSram)
 --
 (bias : Immediate := .float 0) -- Also can be a tensor. Default is none
 (scale : Immediate := .float 1.0) -- This also can accept a tensor
 (_reduce_op : Option AluOp := none)
 (_reduce_res : Option TensorSram := none)
 (reduce_cmd : AccumCmd := .Idle)
 (_mask : Option Immediate := none) := do
  let dstT : TensorRef := .abstract $ .simple dst
  let dataT : TensorRef := .abstract $ .simple data
  let ac : Activate :=  ⟨ dstT, dataT, reduce_cmd, op, scale, bias, .float 0 ⟩ -- FIXME scale is probably wrong
  return .oper [.Activate ac]


--  nki activation_reduce
--   (dst: TensorSram)
--   (op : ActivationFunc)
--   (data : TensorSram)
--   --
--   (reduce_op : Option AluOp := none)
--   (reduce_res : Option TensorSram := none)
--   (bias : Option TensorSram := none)
--   (scale : Sum Immediate TensorSram := .inl (.float 1.0))
--   (mask : Option Immediate := none)
--   (dtype : Option Dtype := none) := do
--      let args := [
--          .activationFunc op,
--          .access (.simple data)
--      ]
--
--      let mut kwargs : List Keyword := []
--
--      kwargs := kwargs ++ match reduce_op with
--      | none => []
--      | some op => [{ name := "reduce_op", value := .aluOp op }]
--
--      kwargs := kwargs ++ match reduce_res with
--      | none => []
--      | some res => [{ name := "reduce_res", value := .access (.simple res) }]
--
--      kwargs := kwargs ++ match bias with
--      | none => []
--      | some b => [{ name := "bias", value := .access (.simple b) }]
--
--      kwargs := kwargs ++ match scale with
--      | .inl imm => [{ name := "scale", value := immediateToValue imm }]
--      | .inr tensor => [{ name := "scale", value := .access (.simple tensor) }]
--
--      if let some m := mask then
--        kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--      -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--      let ty := .tensor dst.dtype dst.shape
--      return .expr (.call "activation_reduce" args kwargs) ty

nki tensor_reduce
  (dst: TensorSram)
  (op : AluOp)
  (data : TensorSram)
  (_axis : Sum Immediate Shape)
  --
  (_mask : Option Immediate := none)
  (_dtype : Option Dtype := none)
  (negate : Bool := false)
  (_keepdims : Bool := false) := do
    let dstT : TensorRef := .abstract $ <-  Access.mkBasic dst []
    let dataT : TensorRef := .abstract $ .simple data
    let opDim := .X -- FIXME - get actual value
    let reduce : TensorReduce := ⟨ dstT, dataT, op, opDim, negate ⟩
    return .oper [.TensorReduce reduce]

-- nki tensor_partition_reduce
--   (dst: TensorSram)
--   (op : AluOp)
--   (data : TensorSram)
--   --
--   (mask : Option Immediate := none)
--   (dtype : Option Dtype := none) := do
--     let args := [
--         .aluOp op,
--         .access (.simple data)
--     ]
--
--     let mut kwargs : List Keyword := [
--         ⟨ "dst", .access (.simple dst) ⟩
--     ]
--
--     if let some m := mask then
--       kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--     -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--     let ty := .tensor dst.dtype dst.shape
--     return .expr (.call "tensor_partition_reduce" args kwargs) ty

-- nki tensor_tensor
--  (dst: TensorSram)
--  (data1 : TensorSram)
--  (data2 : TensorSram)
--  (op : AluOp)
--  --
--  (dtype : Option Dtype := none)
--  (mask : Option Immediate := none)
--  (engine : Engine := Engine.unassigned) := do
--     let args := [
--         .access (.simple data1),
--         .access (.simple data2),
--         .aluOp op
--     ]
--
--     let mut kwargs : List Keyword := [
--         ⟨ "dst", .access (.simple dst) ⟩,
--         ⟨ "engine", engineToValue engine ⟩
--     ]
--
--     if let some m := mask then
--       kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--     -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--     let ty := .tensor dst.dtype dst.shape
--     return .expr (.call "tensor_tensor" args kwargs) ty


nki tensor_tensor_scan
 (dst: TensorSram)
 (data0 : TensorSram)
 (data1 : TensorSram)
 (initial : Sum Immediate TensorSram)
 (op0 : AluOp)
 (op1 : AluOp)
 (reverse0 : Bool := false)
 (reverse1 : Bool := false)
 --
 (_dtype : Option Dtype := none)
 (_mask : Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let data0T : TensorRef := .abstract $ .simple data0
    let data1T : TensorRef := .abstract $ .simple data1
    let rev : TensorScalarReverseOps := converRevOps reverse0 reverse1

    if initial.isRight then
      throw "Tensor initializer is not supported"
    let imm := <- initial.getLeft?

    let tts : TensorTensorScan := ⟨ dstT, data0T, data1T, op0, op1, rev, imm, .Idle ⟩
    return .oper [.TensorTensorScan tts]


-- nki scalar_tensor_tensor
--  (dst : TensorSram)
--  --
--  (data : TensorSram)
--  (op0 : AluOp)
--  (operand0 : Sum Immediate TensorSram)
--  (op1 : AluOp)
--  (operand1 : Sum Immediate TensorSram)
--  (reverse0 : Bool := false)
--  (reverse1 : Bool := false)
--  (dtype : Option Dtype := none)
--  (mask : Option Immediate := none) := do
--     let dstT : TensorRef := .abstract $ .simple dst []
--     let dataT : TensorRef := .abstract $ .simple data []
--     -- let src0T : TensorRef := .abstract $ .simple src0 []
--     -- let src1T : TensorRef := .abstract $ .simple src1 []
--     let rev := converRevOps reverse0 reverse1
--
--     if operand0.isRight then
--       throw "Tensor initializer is not supported"
--     let imm0 := <- operand0.getLeft?
--
--     let stt : ScalarTensorTensor := ⟨ dstT, dataT, src1T, op0, op1, rev, imm0, .Idle ⟩
--     return .oper (.ScalarTensorTensor stt)

-- nki tensor_scalar
--  (dst: TensorSram)
--  (data : TensorSram)
--  (op0 : AluOp)
--  (operand0 : Sum Immediate TensorSram)
--  (reverse0 : Bool := false)
--  (op1 : Option AluOp := none)
--  (operand1 : Option (Sum Immediate TensorSram) := none)
--  (reverse1 : Bool := false)
--  --
--  (dtype : Option Dtype := none)
--  (mask : Option Immediate := none)
--  (engine : Engine := Engine.unassigned) := do
--     let args := [
--         .access (.simple data),
--         .aluOp op0,
--         match operand0 with
--           | .inl i => immediateToValue i
--           | .inr r => .access (.simple r),
--         .bool reverse0,
--         match op1 with
--           | some op => .aluOp op
--           | none => .none,
--         match operand1 with
--           | some operand => match operand with
--             | .inl imm => immediateToValue imm
--             | .inr tensor => .access (.simple tensor)
--           | none => .none,
--         .bool reverse1
--     ]
--
--     let mut kwargs : List Keyword := [
--         ⟨ "dst", .access (.simple dst) ⟩,
--         ⟨ "engine", engineToValue engine ⟩
--     ]
--
--     if let some m := mask then
--       kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--     -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--     let ty := .tensor dst.dtype dst.shape
--     return .expr (.call "tensor_scalar" args kwargs) ty

-- nki tensor_scalar_reduce
--  (dst : TensorSram)
--  --
--  (data : TensorSram)
--  (op0 : AluOp)
--  (operand0 : Sum Immediate TensorSram)
--  (reduce_op : AluOp)
--  (reduce_res : TensorSram)
--  (reverse0 : Bool := false)
--  (dtype : Option Dtype := none)
--  (mask : Option Immediate := none) := do
--     let args := []
--
--     let mut kwargs : List Keyword := [
--         ⟨ "data", .access (.simple data) ⟩,
--         ⟨ "op0", .aluOp op0 ⟩,
--         ⟨ "dst", .access (.simple dst) ⟩,
--         ⟨ "reduce_op", .aluOp reduce_op ⟩,
--         ⟨ "reduce_res", .access (.simple reduce_res) ⟩,
--         ⟨ "reverse0", .bool reverse0 ⟩
--     ]
--
--     kwargs := kwargs ++ match operand0 with
--     | .inl imm => [{ name := "operand0", value := immediateToValue imm }]
--     | .inr tensor => [{ name := "operand0", value := .access (.simple tensor) }]
--
--     if let some m := mask then
--       kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--     -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--     let ty := .tensor dst.dtype dst.shape
--     return .expr (.call "tensor_scalar_reduce" args kwargs) ty


nki tensor_copy
 (dst: TensorSram)
 (src : TensorSram)
 --
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none)
 (_engine : Engine := Engine.unassigned) := do
    let dstT := .abstract $ .simple dst
    let srcT := .abstract $ .simple src
    let copy := ⟨ dstT, srcT, .none ⟩
    return .oper [.Copy copy]

-- nki tensor_copy_dynamic_src
--  (dst : TensorSram)
--  (src : TensorSram)
--  --
--  (mask : Option Immediate := none)
--  (dtype : Option Dtype := none)
--  (engine : Engine := Engine.unassigned) := do
--     let args := [
--         .access (.simple src)
--     ]
--
--     let mut kwargs : List Keyword := [
--         ⟨ "dst", .access (.simple dst) ⟩,
--         ⟨ "engine", engineToValue engine ⟩
--     ]
--
--     if let some m := mask then
--       kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--     -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--     let ty := .tensor dst.dtype dst.shape
--     return .expr (.call "tensor_copy_dynamic_src" args kwargs) ty


-- nki tensor_copy_dynamic_dst
--  --
--  (dst : TensorSram)
--  (src : TensorSram)
--  (mask : Option Immediate := none)
--  (dtype : Option Dtype := none)
--  (engine : Engine := Engine.unassigned) := do
--     let args := []
--
--     let mut kwargs : List Keyword := [
--         ⟨ "src", .access (.simple src) ⟩,
--         ⟨ "dst", .access (.simple dst) ⟩,
--         ⟨ "engine", engineToValue engine ⟩
--     ]
--
--     if let some m := mask then
--       kwargs := kwargs ++ [⟨ "mask", immediateToValue m ⟩]
--
--     -- TODO If dtype is specified, it should call to cast. Cast is currently not implemented
--
--     let ty := .tensor dst.dtype dst.shape
--     return .expr (.call "tensor_copy_dynamic_dst" args kwargs) ty


nki tensor_copy_predicated
 --
 (src : TensorSram)
 (dst : TensorSram)
 (predicate : TensorSram)
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none)
 (_reverse_pred : Bool := false) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src
    let predicateT : TensorRef := .abstract $ .simple predicate
    let cp : CopyPredicated := ⟨ dstT, srcT, predicateT ⟩
    return .oper [.CopyPredicated cp]

nki reciprocal
 (dst: TensorSram)
 (data : TensorSram)
 --
 (_dtype : Option Dtype := none)
 (_mask : Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple data
    return .oper [.Reciprocal ⟨ dstT, srcT ⟩]

nki iota
 (dst: TensorSram)
 (_expr : Int) -- TODO: Placeholder. Figure out this type
 --
 (_dtype : Option Dtype := none)
 (_mask : Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let pattern : DataPattern := ⟨ 0, [] ⟩  -- FIXME
    return .oper [.Iota ⟨ dstT, pattern ⟩]


nki dropout
 (dst: TensorSram)
 (data : TensorSram)
 (prob : Sum Immediate TensorSram)
 --
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let dataT : TensorRef := .abstract $ .simple data

    if prob.isRight then
      throw "Tensor probability is not supported"
    let prob := <- prob.getLeft?

    return .oper [.Dropout ⟨ dstT, dataT, .KeepRate , prob  ⟩]

-- nki affine_select
--  (dst: TensorSram)
--  (pred : Int) -- TODO Placeholder. Figure out this type
--  (on_true_tile : Immediate)
--  (on_false_value : Immediate)
--  --
--  (mask : Option Immediate := none)
--  (dtype : Option Dtype := none) := do
--     let dstT : TensorRef := .abstract $ .simple dst []
--     return .oper $ .AffineSelect ⟨ dst,  ⟩


-- nki range_select
--  (dst: TensorSram)
--  --
--  (on_true_tile : TensorSram)
--  (comp_op0 : AluOp)
--  (comp_op1 : AluOp)
--  (bound0 : TensorSram)
--  (bound1 : TensorSram)
--  (reduce_cmd : AccumCmd := AccumCmd.Idle)
--  (reduce_res : Option TensorSram := none)
--  (reduce_op : AluOp := .max)
--  (range_start : Immediate := .float 0)
--  (on_false_value : Immediate := .float 0)
--  (mask : Option Immediate := none)
--  (dtype : Option Dtype := none) := do
--     let dstT : TensorRef := .abstract $ .simple dst []
--     let succTileT : TensorRef := .absract $ .simple on_true_tile []
--     let rs := ⟨ dstT, succTileT,  ⟩
--     return .oper $ .RangeSelect

nki memset
 (dst: TensorSram)
 (shape : Shape)
 (value : Immediate)
 (_dtype : Dtype)
 --
 (_mask : Option Immediate := none)
 (_engine : Engine := Engine.unassigned) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let ms : MemSet := ⟨ dstT, value, shape.freeElements ⟩ -- TODO: Check with someone
    return .oper [.MemSet ms]

nki bn_stats
 (dst: TensorSram)
 (data : TensorSram)
 --
 (_mask: Option Immediate := none)
 (_dtype: Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let dataT : TensorRef := .abstract $ .simple data
    return .oper [.BatchNormStats ⟨ dstT, dataT ⟩]

nki bn_aggr
 (dst: TensorSram)
 (data : TensorSram)
 --
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let dataT : TensorRef := .abstract $ .simple data
    return .oper [.BatchNormAggregate ⟨ dstT, dataT ⟩]

nki local_gather
 (dst: TensorSram)
 (src_buffer : TensorSram)
 (_index : TensorSram)
 (_num_elem_per_idx : Immediate := .int 1)
 (_num_valid_indices : Option Immediate := none)
 --
 (_mask: Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src_buffer
    return .oper [.LocalGather ⟨ dstT, srcT, .skip, false ⟩]  -- FIXME proper index miss behavior

nki dma_copy
 --
 (dst : TensorSram)
 (src : TensorSram)
 (_mask: Option Immediate := none)
 (dst_rmw_op : Option AluOp := none)
 (_oob_mode : Option Int := none)           -- FIXME: use actual type
 (_dge_mode : Option Int := none) := do     -- FIXME: use actual type
  let dstT : TensorRef := .abstract $ .simple dst
  let srcT : TensorRef := .abstract $ .simple src
  let op : DgeComputeOp := <- match dst_rmw_op with
    | none => .ok .none
    | some rmw_op => match rmw_op with
      | .add => .ok .add
      | _ => throw "Unsupported operation"
  let copy := ⟨ dstT, srcT, op, .disable , .disable ⟩ -- FIXME
  return .oper [.DmaCopy copy]


nki max8
 (dst: TensorSram)
 --
 (src : TensorSram)
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src
    return .oper [.Max8 ⟨ dstT, srcT ⟩]


nki nc_find_index8
 (dst: TensorSram)
 --
 (data : TensorSram)
 (_vals : Int) -- TODO should be a list
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple data
    return .oper [.FindIndex8 ⟨ dstT, srcT ⟩]


nki nc_match_replace8
 (dst: TensorSram)
 --
 (data : TensorSram)
 (_vals : TensorSram) -- A tensor of 8 values to replace
 (imm : Immediate)
 (_dst_idx : Option Int := none) -- Should be an Index
 (_mask: Option Immediate := none)
 (_dtype: Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple data
    return .oper [.MatchReplace8 ⟨ dstT, srcT, imm  ⟩]


nki nc_stream_shuffle
 (src : TensorSram)
 (dst : TensorSram)
 (_shuffle_mask : TensorSram)  -- TODO should be a list
 --
 (_dtype: Option Dtype := none)
 (_mask: Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src
    return .oper [.Shuffle ⟨ dstT, srcT  ⟩]
