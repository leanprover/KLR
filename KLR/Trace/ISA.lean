/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Potapov
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Tensor

namespace KLR.Trace.Isa
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
 (dst : TensorName)
 (stationary : TensorName)
 -- kwargs
 (moving : TensorName)
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
    return .oper [(.loadStationary ls), (.matMul mm)]

nki nc_transpose
 (dst : TensorName)
 (data : TensorName)
 -- kwargs
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none)
 (_engine : Engine := Engine.unassigned) := do
  let dstT : TensorRef := .abstract $ .simple dst
  let srcT : TensorRef := .abstract $ .simple data
  let trn : Transpose := ⟨ dstT, srcT ⟩
  return .oper [.transpose trn]

nki activation
 (dst : TensorName)
 (op : ActivationFunc)
 (data : TensorName)
 --
 (bias : Immediate := .float 0) -- Also can be a tensor. Default is none
 (scale : Immediate := .float 1.0) -- This also can accept a tensor
 (_reduce_op : Option AluOp := none)
 (_reduce_res : Option TensorName := none)
 (reduce_cmd : AccumCmd := .Idle)
 (_mask : Option Immediate := none) := do
  let dstT : TensorRef := .abstract $ .simple dst
  let dataT : TensorRef := .abstract $ .simple data
  let ac : Activate :=  ⟨ dstT, dataT, reduce_cmd, op, scale, bias, .float 0 ⟩ -- FIXME scale is probably wrong
  return .oper [.activate ac]

--  nki activation_reduce
--   (dst: TensorName)
--   (op : ActivationFunc)
--   (data : TensorName)
--   --
--   (reduce_op : Option AluOp := none)
--   (reduce_res : Option TensorName := none)
--   (bias : Option TensorName := none)
--   (scale : Sum Immediate TensorName := .inl (.float 1.0))
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
  (dst: TensorName)
  (op : AluOp)
  (data : TensorName)
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
    return .oper [.tensorReduce reduce]

-- nki tensor_partition_reduce
--   (dst: TensorName)
--   (op : AluOp)
--   (data : TensorName)
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
--  (dst: TensorName)
--  (data1 : TensorName)
--  (data2 : TensorName)
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
 (dst: TensorName)
 (data0 : TensorName)
 (data1 : TensorName)
 (initial : Sum Immediate TensorName)
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
    return .oper [.tensorTensorScan tts]


-- nki scalar_tensor_tensor
--  (dst : TensorName)
--  --
--  (data : TensorName)
--  (op0 : AluOp)
--  (operand0 : Sum Immediate TensorName)
--  (op1 : AluOp)
--  (operand1 : Sum Immediate TensorName)
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
--  (dst: TensorName)
--  (data : TensorName)
--  (op0 : AluOp)
--  (operand0 : Sum Immediate TensorName)
--  (reverse0 : Bool := false)
--  (op1 : Option AluOp := none)
--  (operand1 : Option (Sum Immediate TensorName) := none)
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
--  (dst : TensorName)
--  --
--  (data : TensorName)
--  (op0 : AluOp)
--  (operand0 : Sum Immediate TensorName)
--  (reduce_op : AluOp)
--  (reduce_res : TensorName)
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
 (dst: TensorName)
 (src : TensorName)
 --
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none)
 (_engine : Engine := Engine.unassigned) := do
    let dstT := .abstract $ .simple dst
    let srcT := .abstract $ .simple src
    let copy := ⟨ dstT, srcT, .none ⟩
    return .oper [.copy copy]

-- nki tensor_copy_dynamic_src
--  (dst : TensorName)
--  (src : TensorName)
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
--  (dst : TensorName)
--  (src : TensorName)
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
 (src : TensorName)
 (dst : TensorName)
 (predicate : TensorName)
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none)
 (_reverse_pred : Bool := false) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src
    let predicateT : TensorRef := .abstract $ .simple predicate
    let cp : CopyPredicated := ⟨ dstT, srcT, predicateT ⟩
    return .oper [.copyPredicated cp]

nki reciprocal
 (dst: TensorName)
 (data : TensorName)
 --
 (_dtype : Option Dtype := none)
 (_mask : Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple data
    return .oper [.reciprocal ⟨ dstT, srcT ⟩]

nki iota
 (dst: TensorName)
 (_expr : Int) -- TODO: Placeholder. Figure out this type
 --
 (_dtype : Option Dtype := none)
 (_mask : Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let pattern : DataPattern := ⟨ 0, [] ⟩  -- FIXME
    return .oper [.iota ⟨ dstT, pattern ⟩]


nki dropout
 (dst: TensorName)
 (data : TensorName)
 (prob : Sum Immediate TensorName)
 --
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let dataT : TensorRef := .abstract $ .simple data

    if prob.isRight then
      throw "Tensor probability is not supported"
    let prob := <- prob.getLeft?

    return .oper [.dropout ⟨ dstT, dataT, .KeepRate , prob  ⟩]

-- nki affine_select
--  (dst: TensorName)
--  (pred : Int) -- TODO Placeholder. Figure out this type
--  (on_true_tile : Immediate)
--  (on_false_value : Immediate)
--  --
--  (mask : Option Immediate := none)
--  (dtype : Option Dtype := none) := do
--     let dstT : TensorRef := .abstract $ .simple dst []
--     return .oper $ .AffineSelect ⟨ dst,  ⟩


-- nki range_select
--  (dst: TensorName)
--  --
--  (on_true_tile : TensorName)
--  (comp_op0 : AluOp)
--  (comp_op1 : AluOp)
--  (bound0 : TensorName)
--  (bound1 : TensorName)
--  (reduce_cmd : AccumCmd := AccumCmd.Idle)
--  (reduce_res : Option TensorName := none)
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
 (dst: TensorName)
 (shape : Shape)
 (value : Immediate)
 (_dtype : Dtype)
 --
 (_mask : Option Immediate := none)
 (_engine : Engine := Engine.unassigned) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let ms : MemSet := ⟨ dstT, value, shape.freeElements ⟩ -- TODO: Check with someone
    return .oper [.memSet ms]

nki bn_stats
 (dst: TensorName)
 (data : TensorName)
 --
 (_mask: Option Immediate := none)
 (_dtype: Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let dataT : TensorRef := .abstract $ .simple data
    return .oper [.batchNormStats ⟨ dstT, dataT ⟩]

nki bn_aggr
 (dst: TensorName)
 (data : TensorName)
 --
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let dataT : TensorRef := .abstract $ .simple data
    return .oper [.batchNormAggregate ⟨ dstT, dataT ⟩]

nki local_gather
 (dst: TensorName)
 (src_buffer : TensorName)
 (_index : TensorName)
 (_num_elem_per_idx : Immediate := .int 1)
 (_num_valid_indices : Option Immediate := none)
 --
 (_mask: Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src_buffer
    return .oper [.localGather ⟨ dstT, srcT, .skip, false ⟩]  -- FIXME proper index miss behavior

nki dma_copy
 --
 (dst : TensorName)
 (src : TensorName)
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
  return .oper [.dmaCopy copy]


nki max8
 (dst: TensorName)
 --
 (src : TensorName)
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src
    return .oper [.max8 ⟨ dstT, srcT ⟩]


nki nc_find_index8
 (dst: TensorName)
 --
 (data : TensorName)
 (_vals : Int) -- TODO should be a list
 (_mask : Option Immediate := none)
 (_dtype : Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple data
    return .oper [.findIndex8 ⟨ dstT, srcT ⟩]


nki nc_match_replace8
 (dst: TensorName)
 --
 (data : TensorName)
 (_vals : TensorName) -- A tensor of 8 values to replace
 (imm : Immediate)
 (_dst_idx : Option Int := none) -- Should be an Index
 (_mask: Option Immediate := none)
 (_dtype: Option Dtype := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple data
    return .oper [.matchReplace8 ⟨ dstT, srcT, imm  ⟩]


nki nc_stream_shuffle
 (src : TensorName)
 (dst : TensorName)
 (_shuffle_mask : TensorName)  -- TODO should be a list
 --
 (_dtype: Option Dtype := none)
 (_mask: Option Immediate := none) := do
    let dstT : TensorRef := .abstract $ .simple dst
    let srcT : TensorRef := .abstract $ .simple src
    return .oper [.shuffle ⟨ dstT, srcT  ⟩]
