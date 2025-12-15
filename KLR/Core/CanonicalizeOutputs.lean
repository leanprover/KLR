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

namespace KLR.Core

abbrev NameMap := List (String × String)

def mkNameMap (outputs : List TensorName) : NameMap :=
  outputs.mapIdx fun idx tn => (tn.name, s!"output_{idx}")

def renameStr (m : NameMap) (s : String) : String :=
  m.find? (·.1 == s) |>.map (·.2) |>.getD s

def renameTensor (m : NameMap) (t : TensorName) : Err TensorName :=
  let newName := renameStr m t.name
  let newAddr := { t.address with name := renameStr m t.address.name }
  TensorName.make newName t.dtype t.shape (some newAddr) t.addressRotation

partial def renameAccess (m : NameMap) : Access → Err Access
  | .simple t => return .simple (← renameTensor m t)
  | .basic b => do
    let t ← renameTensor m b.tensor
    AccessBasic.make t b.indexes >>= (return .basic ·)
  | .pattern p => return .pattern { p with tensor := ← renameTensor m p.tensor }
  | .birPattern b => do
    let t ← renameTensor m b.tensor
    let so ← match b.scalarOffset with
      | some (.acc a) => pure $ some (.acc (← renameAccess m a))
      | some (.reg r) => pure $ some (.reg r)
      | none => pure none
    let vo ← b.vectorOffset.mapM (renameAccess m)
    return .birPattern { b with tensor := t, scalarOffset := so, vectorOffset := vo }

def renameTensorRef (m : NameMap) : TensorRef → Err TensorRef
  | .abstract a => return .abstract (← renameAccess m a)
  | other => return other

def renameOperand (m : NameMap) : Operand → Err Operand
  | .tile t => return .tile (← renameTensorRef m t)
  | other => return other

partial def renameOperator (m : NameMap) (op : Operator) : Err Operator := do
  match op with
  | .copy c => return .copy { c with dst := ← renameTensorRef m c.dst, src := ← renameTensorRef m c.src }
  | .ncCopy c => return .ncCopy { c with dst := ← renameTensorRef m c.dst, src := ← renameTensorRef m c.src }
  | .dmaCopy c => return .dmaCopy { c with dst := ← renameTensorRef m c.dst, src := ← renameTensorRef m c.src }
  | .ncDmaCopy c => return .ncDmaCopy { c with dst := ← renameTensorRef m c.dst, src := ← renameTensorRef m c.src }
  | .activate a => return .activate { a with dst := ← renameTensorRef m a.dst, src := ← renameTensorRef m a.src }
  | .ncActivate a => do
      let dst ← renameTensorRef m a.dst
      let src ← renameTensorRef m a.src
      let scale ← renameOperand m a.scale
      let bias ← a.bias.mapM (renameTensorRef m)
      let reduceRes ← a.reduceRes.mapM (renameTensorRef m)
      return .ncActivate { a with dst, src, scale, bias, reduceRes }
  | .tensorTensor t => return .tensorTensor { t with dst := ← renameTensorRef m t.dst, src0 := ← renameTensorRef m t.src0, src1 := ← renameTensorRef m t.src1 }
  | .tensorScalar t => do
      let dst ← renameTensorRef m t.dst
      let src ← renameTensorRef m t.src
      let imm0 ← renameOperand m t.imm0
      let imm1 ← t.imm1.mapM (renameOperand m)
      return .tensorScalar { t with dst, src, imm0, imm1 }
  | .tensorReduce t => return .tensorReduce { t with dst := ← renameTensorRef m t.dst, src := ← renameTensorRef m t.src }
  | .transpose t => return .transpose { t with dst := ← renameTensorRef m t.dst, src := ← renameTensorRef m t.src }
  | .matMul mm => return .matMul { mm with dst := ← renameTensorRef m mm.dst, moving := ← renameTensorRef m mm.moving }
  | .ncMatMul mm => return .ncMatMul { mm with dst := ← renameTensorRef m mm.dst, moving := ← renameTensorRef m mm.moving, stationary := ← renameTensorRef m mm.stationary }
  | .iota i => return .iota { i with dst := ← renameTensorRef m i.dst }
  | .memSet ms => return .memSet { ms with dst := ← renameTensorRef m ms.dst }
  | .shuffle s => return .shuffle { s with dst := ← renameTensorRef m s.dst, src := ← renameTensorRef m s.src }
  | .localGather l => return .localGather { l with dst := ← renameTensorRef m l.dst, src := ← renameTensorRef m l.src }
  | .ncLocalGather l => return .ncLocalGather { l with dst := ← renameTensorRef m l.dst, src := ← renameTensorRef m l.src, index := ← renameTensorRef m l.index }
  | .affineSelect a => return .affineSelect { a with dst := ← renameTensorRef m a.dst, src := ← renameTensorRef m a.src }
  | .ncAffineSelect a => return .ncAffineSelect { a with dst := ← renameTensorRef m a.dst, onTrueTile := ← renameTensorRef m a.onTrueTile }
  | .rangeSelect r => return .rangeSelect { r with dst := ← renameTensorRef m r.dst, src := ← renameTensorRef m r.src }
  | .ncRangeSelect r => do
      let dst ← renameTensorRef m r.dst
      let bound0 ← renameTensorRef m r.bound0
      let bound1 ← renameTensorRef m r.bound1
      let onTrueTile ← renameTensorRef m r.onTrueTile
      let reduceRes ← r.reduceRes.mapM (renameTensorRef m)
      return .ncRangeSelect { r with dst, bound0, bound1, onTrueTile, reduceRes }
  | .dmaTranspose d => return .dmaTranspose { d with dst := ← renameTensorRef m d.dst, src := ← renameTensorRef m d.src }
  | .dropout d => do
      let dst ← renameTensorRef m d.dst
      let src ← renameTensorRef m d.src
      let threshold ← renameOperand m d.threshold
      return .dropout { d with dst, src, threshold }
  | .loadStationary l => return .loadStationary { l with src := ← renameTensorRef m l.src }
  | .scalarTensorTensor s => return .scalarTensorTensor { s with dst := ← renameTensorRef m s.dst, src0 := ← renameTensorRef m s.src0, src1 := ← renameTensorRef m s.src1 }
  | .ncScalarTensorTensor s => do
      let dst ← renameTensorRef m s.dst
      let data ← renameTensorRef m s.data
      let src0 ← renameOperand m s.src0
      let src1 ← renameOperand m s.src1
      return .ncScalarTensorTensor { s with dst, data, src0, src1 }
  | .tensorTensorScan t => do
      let dst ← renameTensorRef m t.dst
      let src0 ← renameTensorRef m t.src0
      let src1 ← renameTensorRef m t.src1
      let imm0 ← renameOperand m t.imm0
      return .tensorTensorScan { t with dst, src0, src1, imm0 }
  | .copyPredicated c => return .copyPredicated { c with dst := ← renameTensorRef m c.dst, src := ← renameTensorRef m c.src, predicate := ← renameTensorRef m c.predicate }
  | .batchNormAggregate b => return .batchNormAggregate { b with dst := ← renameTensorRef m b.dst, src := ← renameTensorRef m b.src }
  | .batchNormStats b => return .batchNormStats { b with dst := ← renameTensorRef m b.dst, src := ← renameTensorRef m b.src }
  | .findIndex8 f => return .findIndex8 { f with dst := ← renameTensorRef m f.dst, src := ← renameTensorRef m f.src, vals := ← renameTensorRef m f.vals }
  | .matchReplace8 mr => do
      let dst ← renameTensorRef m mr.dst
      let src ← renameTensorRef m mr.src
      let vals ← renameTensorRef m mr.vals
      let dstIdx ← mr.dstIdx.mapM (renameTensorRef m)
      return .matchReplace8 { mr with dst, src, vals, dstIdx }
  | .matchValueLoad mv => return .matchValueLoad { mv with src := ← renameTensorRef m mv.src }
  | .max8 mx => return .max8 { mx with dst := ← renameTensorRef m mx.dst, src := ← renameTensorRef m mx.src }
  | .reciprocal r => return .reciprocal { r with dst := ← renameTensorRef m r.dst, src := ← renameTensorRef m r.src }
  | .activationReduce a => do
      let dst ← renameTensorRef m a.dst
      let src ← renameTensorRef m a.src
      let scale ← renameOperand m a.scale
      let bias ← a.bias.mapM (renameTensorRef m)
      let reduceRes ← a.reduceRes.mapM (renameTensorRef m)
      return .activationReduce { a with dst, src, scale, bias, reduceRes }
  | .tensorPartitionReduce t => return .tensorPartitionReduce { t with dst := ← renameTensorRef m t.dst, data := ← renameTensorRef m t.data }
  | .tensorScalarReduce t => do
      let dst ← renameTensorRef m t.dst
      let src ← renameTensorRef m t.src
      let reduceRes ← renameTensorRef m t.reduceRes
      let operand0 ← renameOperand m t.operand0
      return .tensorScalarReduce { t with dst, src, reduceRes, operand0 }
  | .selectReduce s => do
      let dst ← renameTensorRef m s.dst
      let predicate ← renameTensorRef m s.predicate
      let onTrue ← renameTensorRef m s.onTrue
      let onFalse ← renameOperand m s.onFalse
      let reduceRes ← s.reduceRes.mapM (renameTensorRef m)
      return .selectReduce { s with dst, predicate, onTrue, onFalse, reduceRes }
  | .sequenceBounds s => return .sequenceBounds { s with dst := ← renameTensorRef m s.dst, segmentIds := ← renameTensorRef m s.segmentIds }
  | .sendRecv s => return .sendRecv { s with dst := ← renameTensorRef m s.dst, src := ← renameTensorRef m s.src }
  | .sendRecvCCE s => do
      let dst ← renameTensorRef m s.dst
      let src ← s.src.mapM (renameTensorRef m)
      return .sendRecvCCE { s with dst, src }
  | .tensorLoad t => return .tensorLoad { t with src := ← renameTensorRef m t.src }
  | .tensorStore t => return .tensorStore { t with dst := ← renameTensorRef m t.dst }
  | .quantizeMX q => return .quantizeMX { q with dst := ← renameTensorRef m q.dst, src := ← renameTensorRef m q.src, dstScale := ← renameTensorRef m q.dstScale }
  | .ncMatMulMX mm => do
      let dst ← renameTensorRef m mm.dst
      let stationary ← renameTensorRef m mm.stationary
      let moving ← renameTensorRef m mm.moving
      let stationaryScale ← renameTensorRef m mm.stationaryScale
      let movingScale ← renameTensorRef m mm.movingScale
      return .ncMatMulMX { mm with dst, stationary, moving, stationaryScale, movingScale }
  | .dmaCompute d => do
      let dst ← renameTensorRef m d.dst
      let srcs ← d.srcs.mapM (renameTensorRef m)
      return .dmaCompute { d with dst, srcs }
  | .allReduce c => do
      let dsts ← c.dsts.mapM (renameTensorRef m)
      let srcs ← c.srcs.mapM (renameTensorRef m)
      return .allReduce { c with dsts, srcs }
  | .allGather c => do
      let dsts ← c.dsts.mapM (renameTensorRef m)
      let srcs ← c.srcs.mapM (renameTensorRef m)
      return .allGather { c with dsts, srcs }
  | .reduceScatter c => do
      let dsts ← c.dsts.mapM (renameTensorRef m)
      let srcs ← c.srcs.mapM (renameTensorRef m)
      return .reduceScatter { c with dsts, srcs }
  | .collectivePermute c => do
      let dsts ← c.dsts.mapM (renameTensorRef m)
      let srcs ← c.srcs.mapM (renameTensorRef m)
      return .collectivePermute { c with dsts, srcs }
  | .broadcast c => do
      let dsts ← c.dsts.mapM (renameTensorRef m)
      let srcs ← c.srcs.mapM (renameTensorRef m)
      return .broadcast { c with dsts, srcs }
  | .allToAll c => do
      let dsts ← c.dsts.mapM (renameTensorRef m)
      let srcs ← c.srcs.mapM (renameTensorRef m)
      return .allToAll { c with dsts, srcs }
  | .send s => do
      let srcs ← s.srcs.mapM (renameTensorRef m)
      return .send { s with srcs }
  | .recv r => do
      let dsts ← r.dsts.mapM (renameTensorRef m)
      return .recv { r with dsts }
  | .coreBarrier c => return .coreBarrier { c with data := ← renameTensorRef m c.data }
  | .rng r => return .rng { r with dst := ← renameTensorRef m r.dst }
  | .rand2 r => do
      let dst ← renameTensorRef m r.dst
      let min ← renameOperand m r.min
      let max ← renameOperand m r.max
      return .rand2 { r with dst, min, max }
  | .randGetState r => return .randGetState { r with dst := ← renameTensorRef m r.dst }
  | .setRngSeed r => return .setRngSeed { r with src := ← renameTensorRef m r.src }
  | .randSetState r => return .randSetState { r with src := ← renameTensorRef m r.src }
  | .tensorScalarCumulative t => do
      let dst ← renameTensorRef m t.dst
      let src ← renameTensorRef m t.src
      let imm0 ← renameOperand m t.imm0
      let imm1 ← t.imm1.mapM (renameOperand m)
      return .tensorScalarCumulative { t with dst, src, imm0, imm1 }
  | .ncNGather g => return .ncNGather { g with dst := ← renameTensorRef m g.dst, data := ← renameTensorRef m g.data, indices := ← renameTensorRef m g.indices }
  | .devicePrint d => return .devicePrint { d with src := ← renameTensorRef m d.src }
  | other => return other

def renameStmt (m : NameMap) : Stmt → Err Stmt
  | .oper op name pos => return .oper (← renameOperator m op) name pos

def renameBlock (m : NameMap) (b : Block) : Err Block := do
  return { b with body := ← b.body.mapM (renameStmt m) }

def canonicalizeOutputs (k : LncKernel) : Err LncKernel := do
  let m := mkNameMap k.outputs
  let outputs ← k.outputs.mapIdxM fun idx tn =>
    TensorName.make s!"output_{idx}" tn.dtype tn.shape
      (some { tn.address with name := s!"output_{idx}" }) tn.addressRotation
  let bodies ← k.bodies.mapM (·.mapM (renameBlock m))
  return { k with outputs, bodies }
