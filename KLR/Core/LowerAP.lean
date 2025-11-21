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

import KLR.Core.Basic
import KLR.Core.Indexing

/-! # AccessPattern → AP lowering pass -/

namespace KLR.Core

/-- Function to convert an Access to an AccessPattern.
Note: This lowering does not work in all cases, for example, if the Access in an AccessBasic whose
Par dimension takes steps that are not equal to 1. Returns a None in this case. -/
def Access.lowerAccessPattern (a : Access) : KLR.Err BirAccessPattern := do
  -- Don't violate invariants of proved code
  if let .birPattern b := a then
    return b

  -- The layout of a tensor in memory
  -- Note that because accesses are values, we have are forced to assume that all tensors are
  -- laid out in row major form.
  let ap <- Access.toAP a
  if ap.tensor.address.memory != .hbm then
    if ap.parOffset ∉ [0, 32, 64, 96] then
      throw s!"Invalid partition start offset {ap.freeOffset} for non-HBM memory. Valid offsets are: 0, 32, 64, 96"
  let birAp := BirAccessPattern.fromAccessPattern ap
  return birAp

def TensorRef.lowerAccessPatterns : TensorRef → KLR.Err TensorRef
| .abstract a => do return .abstract <| .birPattern (← a.lowerAccessPattern)
| x => do return x

def Operand.lowerAccessPatterns : Operand -> KLR.Err Operand
  | .tile t => do return .tile (<- t.lowerAccessPatterns)
  | x => .ok x

-- TODO: Is there a way to make this less horrible with metaprogramming? All argumetns are of different types.
def Operator.lowerAccessPatterns (k : Operator) : KLR.Err Operator :=
  match k with
  | .activate           op => do return .activate           { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .ncActivate         op => do return .ncActivate         { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), scale := (← op.scale.lowerAccessPatterns), bias := (<- op.bias.mapM TensorRef.lowerAccessPatterns), reduceRes := (<- op.reduceRes.mapM TensorRef.lowerAccessPatterns) }
  | .affineSelect       op => do return .affineSelect       { op with dst := (← op.dst.lowerAccessPatterns), src := (← op.src.lowerAccessPatterns) }
  | .ncAffineSelect     op => do return .ncAffineSelect     { op with dst := (← op.dst.lowerAccessPatterns), onTrueTile := (<- op.onTrueTile.lowerAccessPatterns) }
  | .batchNormAggregate op => do return .batchNormAggregate { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .batchNormStats     op => do return .batchNormStats     { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .copy               op => do return .copy               { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .ncCopy             op => do return .ncCopy             { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .copyPredicated     op => do return .copyPredicated     { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), predicate := (← op.predicate.lowerAccessPatterns) }
  | .dmaCopy            op => do return .dmaCopy            { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .ncDmaCopy          op => do return .ncDmaCopy          { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .dmaTranspose       op => do return .dmaTranspose       { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .dropout            op => do return .dropout            { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), threshold := (← Operand.lowerAccessPatterns op.threshold) }
  | .findIndex8         op => do return .findIndex8         { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), vals := (<- op.vals.lowerAccessPatterns) }
  | .iota               op => do return .iota               { op with dst := (← op.dst.lowerAccessPatterns)}
  | .loadMaskRegister   op => do return .loadMaskRegister   op
  | .loadStationary     op => do return .loadStationary     { op with src := (← op.src.lowerAccessPatterns) }
  | .localGather        op => do return .localGather        { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .ncLocalGather      op => do return .ncLocalGather      { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), index := (<- op.index.lowerAccessPatterns) }
  | .matMul             op => do return .matMul             { op with dst := (← op.dst.lowerAccessPatterns), moving := (← op.moving.lowerAccessPatterns) }
  | .ncMatMul           op => do return .ncMatMul           { op with dst := (← op.dst.lowerAccessPatterns), moving := (← op.moving.lowerAccessPatterns), stationary := (<- op.stationary.lowerAccessPatterns) }
  | .matchReplace8      op => do return .matchReplace8      { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), vals := (<- op.vals.lowerAccessPatterns), dstIdx := (<- op.dstIdx.mapM TensorRef.lowerAccessPatterns) }
  | .matchValueLoad     op => do return .matchValueLoad     { op with src := (← op.src.lowerAccessPatterns) }
  | .max8               op => do return .max8               { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .memSet             op => do return .memSet             { op with dst := (← op.dst.lowerAccessPatterns) }
  | .rangeSelect        op => do return .rangeSelect        { op with dst := (← op.dst.lowerAccessPatterns), src := (<- op.src.lowerAccessPatterns) }
  | .ncRangeSelect      op => do return .ncRangeSelect      { op with dst := (← op.dst.lowerAccessPatterns), reduceRes := (← op.reduceRes.mapM TensorRef.lowerAccessPatterns), bound0 := (← op.bound0.lowerAccessPatterns) , bound1 := (← op.bound1.lowerAccessPatterns), onTrueTile := (<- op.onTrueTile.lowerAccessPatterns)  }
  | .reciprocal         op => do return .reciprocal         { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .scalarTensorTensor op => do return .scalarTensorTensor { op with dst := (← op.dst.lowerAccessPatterns), src0 := (← op.src0.lowerAccessPatterns), src1 := (← op.src1.lowerAccessPatterns) }
  | .ncScalarTensorTensor op => do return .ncScalarTensorTensor { op with dst := (← op.dst.lowerAccessPatterns), data := (← op.data.lowerAccessPatterns), src0 := (← op.src0.lowerAccessPatterns), src1 := (← op.src1.lowerAccessPatterns) }
  | .shuffle            op => do return .shuffle            { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .tensorReduce       op => do return .tensorReduce       { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .tensorScalar       op => do return .tensorScalar       { op with src := (← op.src.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns), imm0 := (← Operand.lowerAccessPatterns op.imm0), imm1 := (← op.imm1.mapM Operand.lowerAccessPatterns) }
  | .tensorTensor       op => do return .tensorTensor       { op with src0 := (← op.src0.lowerAccessPatterns), src1 := (← op.src1.lowerAccessPatterns), dst := (← op.dst.lowerAccessPatterns) }
  | .tensorTensorScan   op => do return .tensorTensorScan   { op with dst := (← op.dst.lowerAccessPatterns), src0 := (← op.src0.lowerAccessPatterns), src1 := (← op.src1.lowerAccessPatterns), imm0 := (← Operand.lowerAccessPatterns op.imm0) }
  | .transpose          op => do return .transpose          { op with src := (← op.src.lowerAccessPatterns), dst := (<- op.dst.lowerAccessPatterns) }
  | .activationReduce   op => do
    return .activationReduce { op with
      dst := (<- op.dst.lowerAccessPatterns)
      src := (<- op.src.lowerAccessPatterns)
      reduceRes := (<- op.reduceRes.mapM TensorRef.lowerAccessPatterns)
      bias := (<- op.bias.mapM TensorRef.lowerAccessPatterns)
    }
  | .tensorPartitionReduce op => do
    return .tensorPartitionReduce {op with
     dst := (<- op.dst.lowerAccessPatterns)
     data := (<- op.data.lowerAccessPatterns)
    }
  | .tensorScalarReduce op => do
    return .tensorScalarReduce { op with
     dst := (<- op.dst.lowerAccessPatterns)
     src := (<- op.src.lowerAccessPatterns)
     operand0 := (← Operand.lowerAccessPatterns op.operand0)
     reduceRes := (<- op.reduceRes.lowerAccessPatterns)
    }
  | .selectReduce op => do
    return .selectReduce { op with
      dst := (<- op.dst.lowerAccessPatterns)
      predicate := (<- op.predicate.lowerAccessPatterns)
      onTrue := (<- op.onTrue.lowerAccessPatterns)
      onFalse := (<- op.onFalse.lowerAccessPatterns)
      reduceRes := (<- op.reduceRes.mapM TensorRef.lowerAccessPatterns)
    }
  | .sequenceBounds op => do
    return .sequenceBounds { op with
      dst := (<- op.dst.lowerAccessPatterns)
      segmentIds := (<- op.segmentIds.lowerAccessPatterns)
    }
  | .sendRecv op => do return .sendRecv { op with dst := (<- op.dst.lowerAccessPatterns), src := (<- op.src.lowerAccessPatterns)}
  | .sendRecvCCE op => do return .sendRecvCCE { op with
    dst := (<-op.dst.lowerAccessPatterns)
    src := (<- op.src.mapM TensorRef.lowerAccessPatterns)
    }
  | .tensorStore op => return .tensorStore { op with
    dst := <- op.dst.lowerAccessPatterns
    }
  | .tensorLoad op => return .tensorLoad { op with
    src := <- op.src.lowerAccessPatterns
    }
  | .registerMove ..
  | .cmpBranch ..
  | .registerAluOp .. => return k
  | .quantizeMX op => return .quantizeMX { op with
      dst := (<- op.dst.lowerAccessPatterns),
      src := (<- op.src.lowerAccessPatterns),
      dstScale := (<- op.dstScale.lowerAccessPatterns)
    }
  | .ncMatMulMX op => return .ncMatMulMX { op with
      dst := (<- op.dst.lowerAccessPatterns),
      stationary := (<- op.stationary.lowerAccessPatterns),
      moving := (<- op.moving.lowerAccessPatterns),
      stationaryScale := (<- op.stationaryScale.lowerAccessPatterns),
      movingScale := (<- op.movingScale.lowerAccessPatterns)
    }
  | .dmaCompute op => return .dmaCompute { op with
      dst := (<- op.dst.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .allReduce op => return .allReduce { op with
      dsts := (<- op.dsts.mapM TensorRef.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .allGather op => return .allGather { op with
      dsts := (<- op.dsts.mapM TensorRef.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .reduceScatter op => return .reduceScatter { op with
      dsts := (<- op.dsts.mapM TensorRef.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .collectivePermute op => return .collectivePermute { op with
      dsts := (<- op.dsts.mapM TensorRef.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .broadcast op => return .broadcast { op with
      dsts := (<- op.dsts.mapM TensorRef.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .allToAll op => return .allToAll { op with
      dsts := (<- op.dsts.mapM TensorRef.lowerAccessPatterns),
      srcs := (<- op.srcs.mapM TensorRef.lowerAccessPatterns),
    }
  | .send s => return .send { s with
      srcs := (<- s.srcs.mapM TensorRef.lowerAccessPatterns)
    }
  | .recv r => return .recv { r with
      dsts := (<- r.dsts.mapM TensorRef.lowerAccessPatterns)
    }
  | .coreBarrier c => return .coreBarrier { c with
    data := (<- c.data.lowerAccessPatterns)
  }
  | .rng r => return .rng { r with dst := (<- r.dst.lowerAccessPatterns)}
  | .rand2 r => return .rand2 {
      dst := <- r.dst.lowerAccessPatterns
      min := <- r.min.lowerAccessPatterns
      max := <- r.max.lowerAccessPatterns
      }
  | .randGetState r => return .randGetState { r with dst := (<- r.dst.lowerAccessPatterns)}
  | .setRngSeed r => return .setRngSeed { r with src := (<- r.src.lowerAccessPatterns)}
  | .randSetState r => return .randSetState { r with src := (<- r.src.lowerAccessPatterns)}
  | .extendedInst i => return .extendedInst i
  | .tensorScalarCumulative op => return .tensorScalarCumulative { op with
      dst := <- op.dst.lowerAccessPatterns
      src := <- op.src.lowerAccessPatterns
      imm0 := <- Operand.lowerAccessPatterns op.imm0
      imm1 := <- op.imm1.mapM Operand.lowerAccessPatterns
    }

def Stmt.lowerAccessPatterns : Stmt → KLR.Err Stmt
  | .oper op name pos => return .oper (<- op.lowerAccessPatterns) name pos

def Block.lowerAccessPatterns (b : Block) : KLR.Err Block := do
  let body <- b.body.mapM Stmt.lowerAccessPatterns
  return { b with body := body }

def Kernel.lowerAccessPatterns (k : Kernel) : KLR.Err Kernel := do
  let body' ← k.body.mapM Block.lowerAccessPatterns
  return { k with body := body'}

def lowerAccessPatterns (k : LncKernel) : KLR.Err LncKernel := do
  let mut bodies := []
  for body in k.bodies do
    let body' ← body.mapM Block.lowerAccessPatterns
    bodies := body' :: bodies
  return { k with bodies := bodies.reverse }
