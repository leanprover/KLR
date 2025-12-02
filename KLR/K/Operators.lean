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

import KLR.Core.Tensor
import KLR.Core.Operators
import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util
import Lean

/-
# Definition of operators

These definitions follow the hardware ISA as close as possible.
-/
namespace KLR.K
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

/- Registers shouldn't be exposed in the Operator interface, they should be an
implementation detail of one of the lower level languages like K1. However, some
of these instructions take registers in weird ways we haven't fully investigated yet,
so for now we use Nat as a placeholder.
-/
def Reg := Nat
deriving BEq, Inhabited, Repr, Nonempty
instance : ToString Reg where
  toString reg := s!"reg({repr reg})"

/-
Used for Iota and AffineSelect, represents something similar to an
TensorSram but that is only used to generate data, not to index. Much like
LEA in x86.
-/
structure DataPattern (Scalar : Type) where
  offset  : Scalar
  pattern  : List KLR.Core.APPair
  deriving BEq, Repr
instance [ToString Scalar] : ToString (DataPattern Scalar) where
  toString op :=
    s!"DataPattern(offset={op.offset}, pattern={repr op.pattern})"

/- Whether the dropout rate is how many values should be dropped or how many
values should be kept -/
inductive DropoutThresholdType
  | DropRate
  | KeepRate
  deriving BEq, Repr

/- Control how data is accumulated at destination locations -/
inductive AccumCmd where
  | Idle
  | Zero
  | Accumulate
  | ZeroAccumulate
  | LoadAccumulate
  deriving BEq, Repr

inductive ActivationFunc where
  | abs
  | arctan
  | copy
  | erf
  | erf_dx
  | exp
  | gelu
  | gelu_apprx_tanh
  | gelu_dx
  | log
  | mish
  | reciprocal
  | relu
  | rsqrt
  | sigmoid
  | sign
  | silu
  | silu_dx
  | sin
  | softplus
  | sqrt
  | square
  | tanh
  | gelu_apprx_sigmoid
  | gelu_apprx_sigmoid_dx
  deriving BEq, Repr, Inhabited, Repr, Nonempty

/- The comparator for an affine select -/
inductive AffineSelectCmp where
  | GreaterThan
  | GreaterThanEq
  | Eq
  | NotEq
  deriving BEq, Repr

/- RMW ops for DMA -/
inductive DgeComputeOp where
  | none
  | add
  deriving BEq, Repr

/- The DMA bounds check flag can either be an immediate or in a register -/
inductive DmaBounds where
  | disable
  | enable
  | reg (reg : Reg)
  deriving BEq, Repr

/- Indicates whether this is the first, middle, or last matmul
instruction in a series of instructions that are accumulating into a region
of psum -/
inductive MatmulGroupElement where
  | first
  | middle
  | last
  | whole
  deriving BEq, Repr

/- Whether an immediate should be written, or nothing should be written, when an index misses -/
inductive IndexMissBehavior (Scalar : Type) where
  | imm (value : Scalar)
  | skip
  deriving BEq, Repr

/- Which of the ops to TensorScalar should be reversed (only matters for
non-commutative operators)-/
inductive TensorScalarReverseOps where
  | none
  | first
  | second
  | both
  deriving BEq, Repr

/- A representation of a contiguous set of axes of a tensor -/
inductive TensorSubDim where
  /- The last axis -/
  | X
  /- The last two axes -/
  | XY
  /- The last three axes -/
  | XYZ
  /- The last four axes -/
  | XYZW
  deriving BEq, Repr

def TensorSubDim.IsCopySubDim : TensorSubDim → Prop
| X => True | _ => False

/- Dropout instruction -/
structure Dropout (Tensor : Type) (Scalar : Type) where
  dst           : Tensor
  src           : Tensor
  thresholdType : DropoutThresholdType
  threshold     : Scalar
  deriving BEq, Repr

/- Activate instruction

Performs the operation
`OUT accum= activate_func( (IN * scale_value) + bias, imm )`
-/
structure Activate (Tensor : Type) (Scalar : Type) where
  dst             : Tensor
  src             : Tensor
  accumulatorCmd  : AccumCmd
  activationFunc  : ActivationFunc
  scale           : Scalar
  bias            : Scalar
  imm             : Scalar
  deriving BEq, Repr

/- AffineSelect instruction

Generates values using the `maskPattern` and runs them through `op`. If
the comparison is true, the value from `in` is used, otherwise `fill_value` is used.
out[k] = (mask[k] <op> 0) ? in[k]  : fill_value
-/
structure AffineSelect (Tensor : Type) (Scalar : Type) where
  dst         : Tensor
  src         : Tensor
  fillMode    : AffineSelectCmp
  fillReg     : Reg
  maskPattern : DataPattern Scalar
  deriving BEq, Repr

/- DmaCopy instruction

Generate descriptors to use the DMA to perform a copy. This is only used
for sbuf/psum transfers. For interacting with the HBM, use DmaHbmLoad/Store

TODO: this operation is stateful since it uses the DMA queues. How
do we represent that at the KLR level?
-/
structure DmaCopy (Tensor : Type) (Scalar : Type) where
  dst            : Tensor
  src            : Tensor
  compute_op     : DgeComputeOp
  dstBoundsCheck : DmaBounds
  srcBoundsCheck : DmaBounds
  deriving BEq, Repr

/- DmaTranspose instruction
Use the DMA to reverse the dimensions of a tensor.
-/
structure DmaTranspose (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- Transpose Instruction

Uses the DVE engine to do a transpose on 32x32 tiles of tensors up to 4d.
The total size of the accesses must be a multiple of 32x32, and the src and dest
must be the same size. The number of partitions must be a multiple of 32.
-/
structure Transpose (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- LoadMaskRegister instruction

Sets a register to be the MaskRegister in the DVE
-/
structure LoadMaskRegister (Tensor : Type) (Scalar : Type) where
  regNum : Reg
  deriving BEq, Repr

/-
Use the DVE to shuffle the data in src into dst based on MaskRegister
-/
structure Shuffle (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- MemSet instruction

Sets `count` elements of `dst` to `value`
-/
structure MemSet (Tensor : Type) (Scalar : Type) where
  dst   : Tensor
  value : Scalar
  count : Nat
  deriving BEq, Repr

/- Iota Instruction
Generates values using `pattern` and writes them to `dst` -/
structure Iota (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  pattern : DataPattern Scalar
  deriving BEq, Repr

/- LoadStationary Instruction

Loads a matrix into the PE.
-/
structure LoadStationary (Tensor : Type) (Scalar : Type) where
  src         : Tensor
  isTranspose : Bool
  deriving BEq, Repr

/- MatMul instruction

Performs a matmul against the currently loaded tensor using the PE -/
structure MatMul (Tensor : Type) (Scalar : Type) where
  dst                : Tensor
  moving             : Tensor
  psumAccumulateFlag : MatmulGroupElement
  deriving BEq, Repr

/- LocalGather instruction
-/
structure LocalGather (Tensor : Type) (Scalar : Type) where
  dst               : Tensor
  src               : Tensor
  indexMissBehavior : IndexMissBehavior Scalar
  /- Set to true when this is the last local gather operation in a group
  to free the pool buffer -/
  freePoolBuffer    : Bool
  deriving BEq, Repr

/- RangeSelect instruction
-/
structure RangeSelect (Tensor : Type) (Scalar : Type) where
  dst            : Tensor
  src            : Tensor
  reduceCommand  : AccumCmd
  reduceOp       : KLR.Core.AluOp
  base           : Float32
  fillValue      : Float32
  compOp0        : KLR.Core.AluOp
  compOp1        : KLR.Core.AluOp
  bound0         : Scalar
  bound1         : Scalar
  deriving BEq, Repr

/- ScalarTensorTensor instruction

```
if accumulator_cmd == ZeroAccumulator:
    accum_value = 0
scalar_result = src0 op_0 imm0 # broadcast imm0 onto src0
dst = scalar_result op_1 src1
if (accumulator_cmd == ZeroAccumulator) or (accumulator_cmd == Accumulator):
    accum_value += dst
```
-/
structure ScalarTensorTensor (Tensor : Type) (Scalar : Type) where
  dst             : Tensor
  src0            : Tensor
  src1            : Tensor
  op0             : KLR.Core.AluOp
  op1             : KLR.Core.AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Scalar
  accumulatorCmd  : AccumCmd
  deriving BEq, Repr

/- CopyPredicated instruction

Copies each element from src to dst for which predicate is not 0 -/
structure CopyPredicated (Tensor : Type) (Scalar : Type) where
  dst       : Tensor
  src       : Tensor
  predicate : Tensor
  deriving BEq, Repr

/- TensorTensorScan instruction

for lane_id in range(num_active_channels):
    internal_state = imm0
    for src0_elem, src1_elem in packed(src0_mem_pattern, src1_mem_pattern):
        new_result = (src0_elem op0 internal_state) op1 src1_elem
        internal_state = new_result
        dst_mem_pattern.append(new_result)
-/
structure TensorTensorScan (Tensor : Type) (Scalar : Type) where
  dst             : Tensor
  src0            : Tensor
  src1            : Tensor
  op0             : KLR.Core.AluOp
  op1             : KLR.Core.AluOp
  reverseOperands : TensorScalarReverseOps
  imm0            : Scalar
  accumulatorCmd  : AccumCmd
  deriving BEq, Repr

/- MatchValueLoad instruction

Loads values into the DVE's MatchValue registers -/
structure MatchValueLoad (Tensor : Type) (Scalar : Type) where
  src : Tensor
  deriving BEq, Repr


/- FindIndex8 instruction

For each element in MatchValue register, find the first element of src that
matches and stores its index in dst. -/
structure FindIndex8 (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- MatchReplace8 instruction

Same as FindIndex8, but replaces the found values in src with `replaceValue`-/
structure MatchReplace8 (Tensor : Type) (Scalar : Type) where
  dst          : Tensor
  src          : Tensor
  replaceValue : Scalar
  deriving BEq, Repr

/- Max8 instruction

Finds the 8 largest values in src and writes them to dst -/
structure Max8 (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- BatchNormAggregate instruction
-/
structure BatchNormAggregate (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- BatchNormStats instruction
-/
structure BatchNormStats (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

/- Reciprocal instruction
-/
structure Reciprocal (Tensor : Type) (Scalar : Type) where
  dst  : Tensor
  src  : Tensor
  deriving BEq, Repr

/- Copy instruction
Copy src to dst -/
structure Copy (Tensor : Type) (Scalar : Type) where
  dst   : Tensor
  src   : Tensor
  /- TODO: what is this for? -/
  opDim : Option TensorSubDim
  deriving BEq, Repr

/- TensorReduce instruction

Reduces a tensor along specified dimensions -/
structure TensorReduce (Tensor : Type) (Scalar : Type) where
  dst          : Tensor
  src          : Tensor
  op           : KLR.Core.AluOp
  opDim        : TensorSubDim
  -- the negated field is only relevant for arithmetic operations
  negated      : Bool
  deriving BEq, Repr

/- TensorScalar instruction

output[k] = (input[k] <op0> imm0) <op1> imm1
-/
structure TensorScalar (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  imm0 : Scalar
  op0 : KLR.Core.AluOp
  imm1 : Scalar
  op1 : KLR.Core.AluOp
  reverse : TensorScalarReverseOps
  deriving BEq, Repr

/- TensorTensor instruction
-/
structure TensorTensor (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src0 : Tensor
  src1 : Tensor
  op : KLR.Core.AluOp
  deriving BEq, Repr

structure Identity (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

structure Reshape (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  deriving BEq, Repr

structure MatMulP (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  a   : Tensor
  b   : Tensor
  deriving BEq, Repr, Inhabited, Nonempty

structure TransposeP (Tensor : Type) (Scalar : Type) where
  dst : Tensor
  src : Tensor
  dims : List Nat
  deriving BEq, Repr, Inhabited, Nonempty

inductive Operator (Tensor : Type) (Scalar : Type) where
  | activate (op : Activate Tensor Scalar)
  | affineSelect (op : AffineSelect Tensor Scalar)
  | batchNormAggregate (op : BatchNormAggregate Tensor Scalar)
  | batchNormStats (op : BatchNormStats Tensor Scalar)
  | copy (op : Copy Tensor Scalar)
  | copyPredicated (op : CopyPredicated Tensor Scalar)
  | dmaCopy (op : DmaCopy Tensor Scalar)
  | dmaTranspose (op : DmaTranspose Tensor Scalar)
  | dropout (op : Dropout Tensor Scalar)
  | findIndex8 (op : FindIndex8 Tensor Scalar)
  | iota (op : Iota Tensor Scalar)
  | loadMaskRegister (op : LoadMaskRegister Tensor Scalar)
  | loadStationary (op : LoadStationary Tensor Scalar)
  | localGather (op : LocalGather Tensor Scalar)
  | matMul (op : MatMul Tensor Scalar)
  | matchReplace8 (op : MatchReplace8 Tensor Scalar)
  | matchValueLoad (op : MatchValueLoad Tensor Scalar)
  | max8 (op : Max8 Tensor Scalar)
  | memSet (op : MemSet Tensor Scalar)
  | rangeSelect (op : RangeSelect Tensor Scalar)
  | reciprocal (op : Reciprocal Tensor Scalar)
  | scalarTensorTensor (op : ScalarTensorTensor Tensor Scalar)
  | shuffle (op : Shuffle Tensor Scalar)
  | tensorReduce (op : TensorReduce Tensor Scalar)
  | tensorScalar (op : TensorScalar Tensor Scalar)
  | tensorTensor (op : TensorTensor Tensor Scalar)
  | tensorTensorScan (op : TensorTensorScan Tensor Scalar)
  | transpose (op : Transpose Tensor Scalar)

  | matmulP (op : MatMulP Tensor Scalar)
  | reshapeP (op : Reshape Tensor Scalar)
  | identityP (op : Identity Tensor Scalar)
  | transposeP (op : TransposeP Tensor Scalar)
  deriving BEq, Repr, Inhabited, Nonempty, Repr

instance {Tensor Scalar : Type} [ToString Tensor] [ToString Scalar] : ToString (Operator Tensor Scalar) where
  toString op := match op with
    | .activate ⟨dst, src, accumulatorCmd, activationFunc, scale, bias, imm⟩ =>
        s!"{dst} = activate({src}, {repr accumulatorCmd}, {repr activationFunc}, {scale}, {bias}, {imm})"
    | .affineSelect ⟨dst, src, fillMode, fillReg, maskPattern⟩ =>
        s!"{dst} = affineSelect({src}, {repr fillMode}, {fillReg}, {maskPattern})"
    | .batchNormAggregate ⟨dst, src⟩ =>
        s!"{dst} = batchNormAggregate({src})"
    | .batchNormStats ⟨dst, src⟩ =>
        s!"{dst} = batchNormStats({src})"
    | .copy ⟨dst, src, opDim⟩ =>
        s!"{dst} = copy({src}, {repr opDim})"
    | .copyPredicated ⟨dst, src, predicate⟩ =>
        s!"{dst} = copyPredicated({src}, {predicate})"
    | .dmaCopy ⟨dst, src, compute_op, dstBoundsCheck, srcBoundsCheck⟩ =>
        s!"{dst} = dmaCopy({src}, {repr compute_op}, {repr dstBoundsCheck}, {repr srcBoundsCheck})"
    | .dmaTranspose ⟨dst, src⟩ =>
        s!"{dst} = dmaTranspose({src})"
    | .dropout ⟨dst, src, thresholdType, threshold⟩ =>
        s!"{dst} = dropout({src}, {repr thresholdType}, {threshold})"
    | .findIndex8 ⟨dst, src⟩ =>
        s!"{dst} = findIndex8({src})"
    | .iota ⟨dst, pattern⟩ =>
        s!"{dst} = iota({pattern})"
    | .loadMaskRegister ⟨regNum⟩ =>
        s!"{regNum} = loadMaskRegister()"
    | .loadStationary ⟨src, isTranspose⟩ =>
        s!"= loadStationary({src}, {isTranspose})"
    | .localGather ⟨dst, src, _, freePoolBuffer⟩ =>
        s!"{dst} = localGather({src}, ..., {freePoolBuffer})"
    | .matMul ⟨dst, moving, psumAccumulateFlag⟩ =>
        s!"{dst} = matMul({moving}, {repr psumAccumulateFlag})"
    | .matchReplace8 ⟨dst, src, replaceValue⟩ =>
        s!"{dst} = matchReplace8({src}, {replaceValue})"
    | .matchValueLoad ⟨src⟩ =>
        s!"= matchValueLoad({src})"
    | .max8 ⟨dst, src⟩ =>
        s!"{dst} = max8({src})"
    | .memSet ⟨dst, value, count⟩ =>
        s!"{dst} = memSet({value}, {count})"
    | .rangeSelect ⟨dst, src, reduceCommand, reduceOp, base, fillValue, compOp0, compOp1, bound0, bound1⟩ =>
        s!"{dst} = rangeSelect({src}, {repr reduceCommand}, {reduceOp}, {base}, {fillValue}, {compOp0}, {compOp1}, {bound0}, {bound1})"
    | .reciprocal ⟨dst, src⟩ =>
        s!"{dst} = reciprocal({src})"
    | .scalarTensorTensor ⟨dst, src0, src1, op0, op1, reverse, imm0, accumulatorCmd⟩ =>
        s!"{dst} = scalarTensorTensor({src0}, {src1}, {op0}, {op1}, {repr reverse}, {imm0}, {repr accumulatorCmd})"
    | .shuffle ⟨dst, src⟩ =>
        s!"{dst} = shuffle({src})"
    | .tensorReduce ⟨dst, src, op, opDim, negated⟩ =>
        s!"{dst} = tensorReduce({src}, {op}, {repr opDim}, {negated})"
    | .tensorScalar ⟨dst, src, imm0, op0, imm1, op1, reverse⟩ =>
        s!"{dst} = tensorScalar({src}, {imm0}, {op0}, {imm1}, {op1}, {repr reverse})"
    | .tensorTensor ⟨dst, src0, src1, op⟩ =>
        s!"{dst} = tensorTensor({src0}, {src1}, {op})"
    | .tensorTensorScan ⟨dst, src0, src1, op0, op1, reverseOperands, imm0, accumulatorCmd⟩ =>
        s!"{dst} = tensorTensorScan({src0}, {src1}, {op0}, {op1}, {repr reverseOperands}, {imm0}, {repr accumulatorCmd})"
    | .transpose ⟨dst, src⟩ =>
        s!"{dst} = transpose({src})"
    | .matmulP ⟨dst, a, b⟩ =>
        s!"{dst} = matmul({a}, {b})"
    | .reshapeP ⟨dst, src⟩ =>
        s!"{dst} = reshape({src})"
    | .identityP ⟨dst, src⟩ =>
        s!"{dst} = identity({src})"
    | .transposeP ⟨dst, src, dims⟩ =>
        s!"{dst} = transposeP({src}, {dims})"

/- The list of tensors used by an operator -/
def dependencies : Operator Tensor Scalar -> List Tensor
| .activate ⟨_, src, _, _, _, _, _⟩ => [src]
| .affineSelect ⟨_, src, _, _, _⟩ => [src]
| .batchNormAggregate ⟨_, src⟩ => [src]
| .batchNormStats ⟨_, src⟩ => [src]
| .copy ⟨_, src, _⟩ => [src]
| .copyPredicated ⟨_, src, _⟩ => [src]
| .dmaCopy ⟨_, src, _, _, _⟩ => [src]
| .dmaTranspose ⟨_, src⟩ => [src]
| .dropout ⟨_, src, _, _⟩ => [src]
| .findIndex8 ⟨_, src⟩ => [src]
| .iota ⟨_, _⟩ => []
| .loadMaskRegister ⟨_⟩ => []
| .loadStationary ⟨src, _⟩ => [src]
| .localGather ⟨_, src, _, _⟩ => [src]
| .matMul ⟨_, moving, _⟩ => [moving]
| .matchReplace8 ⟨_, src, _⟩ => [src]
| .matchValueLoad ⟨src⟩ => [src]
| .max8 ⟨_, src⟩ => [src]
| .memSet ⟨_, _, _⟩ => []
| .rangeSelect ⟨_, src, _, _, _, _, _, _, _, _⟩ => [src]
| .reciprocal ⟨_, src⟩ => [src]
| .scalarTensorTensor ⟨_, src0, src1, _, _, _, _, _⟩ =>
    [src0, src1]
| .shuffle ⟨_, src⟩ => [src]
| .tensorReduce ⟨_, src, _, _, _⟩ => [src]
| .tensorScalar ⟨_, src, _, _, _, _, _⟩ =>
    [src]
| .tensorTensor ⟨_, src0, src1, _⟩ =>
    [src0, src1]
| .tensorTensorScan ⟨_, src0, src1, _, _, _, _, _⟩ =>
    [src0, src1]
| .transpose ⟨_, src⟩ => [src]
| .matmulP ⟨_, a, b⟩ => [a, b]
| .reshapeP ⟨_, src⟩ => [src]
| .identityP ⟨_, src⟩ => [src]
| .transposeP ⟨_, src, _⟩ => [src]

/- The list of tensors defined by an operator -/
def targets : Operator Tensor Scalar -> List Tensor
| .activate ⟨dst, _, _, _, _, _, _⟩ => [dst]
| .affineSelect ⟨dst, _, _, _, _⟩ => [dst]
| .batchNormAggregate ⟨dst, _⟩ => [dst]
| .batchNormStats ⟨dst, _⟩ => [dst]
| .copy ⟨dst, _, _⟩ => [dst]
| .copyPredicated ⟨dst, _, _⟩ => [dst]
| .dmaCopy ⟨dst, _, _, _, _⟩ => [dst]
| .dmaTranspose ⟨dst, _⟩ => [dst]
| .dropout ⟨dst, _, _, _⟩ => [dst]
| .findIndex8 ⟨dst, _⟩ => [dst]
| .iota ⟨dst, _⟩ => [dst]
| .loadMaskRegister ⟨_⟩ => []
| .loadStationary ⟨_, _⟩ => []
| .localGather ⟨dst, _, _, _⟩ => [dst]
| .matMul ⟨dst, _, _⟩ => [dst]
| .matchReplace8 ⟨dst, _, _⟩ => [dst]
| .matchValueLoad ⟨_⟩ => []
| .max8 ⟨dst, _⟩ => [dst]
| .memSet ⟨dst, _, _⟩ => [dst]
| .rangeSelect ⟨dst, _, _, _, _, _, _, _, _, _⟩ => [dst]
| .reciprocal ⟨dst, _⟩ => [dst]
| .scalarTensorTensor ⟨dst, _, _, _, _, _, _, _⟩ => [dst]
| .shuffle ⟨dst, _⟩ => [dst]
| .tensorReduce ⟨dst, _, _, _, _⟩ => [dst]
| .tensorScalar ⟨dst, _, _, _, _, _, _⟩ => [dst]
| .tensorTensor ⟨dst, _, _, _⟩ => [dst]
| .tensorTensorScan ⟨dst, _, _, _, _, _, _, _⟩ => [dst]
| .transpose ⟨dst, _⟩ => [dst]
| .matmulP ⟨dst, _, _⟩ => [dst]
| .reshapeP ⟨dst, _⟩ => [dst]
| .identityP ⟨dst, _⟩ => [dst]
| .transposeP ⟨dst, _, _⟩ => [dst]

def name : Operator Tensor Scalar -> String
| .activate _ => "activate"
| .affineSelect _ => "affineSelect"
| .batchNormAggregate _ => "batchNormAggregate"
| .batchNormStats _ => "batchNormStats"
| .copy _ => "copy"
| .copyPredicated _ => "copyPredicated"
| .dmaCopy _ => "dmaCopy"
| .dmaTranspose _ => "dmaTranspose"
| .dropout _ => "dropout"
| .findIndex8 _ => "findIndex8"
| .iota _ => "iota"
| .loadMaskRegister _ => "loadMaskRegister"
| .loadStationary _ => "loadStationary"
| .localGather _ => "localGather"
| .matMul _ => "matMul"
| .matchReplace8 _ => "matchReplace8"
| .matchValueLoad _ => "matchValueLoad"
| .max8 _ => "max8"
| .memSet _ => "memSet"
| .rangeSelect _ => "rangeSelect"
| .reciprocal _ => "reciprocal"
| .scalarTensorTensor _ => "scalarTensorTensor"
| .shuffle _ => "shuffle"
| .tensorReduce _ => "tensorReduce"
| .tensorScalar _ => "tensorScalar"
| .tensorTensor _ => "tensorTensor"
| .tensorTensorScan _ => "tensorTensorScan"
| .transpose _ => "transpose"
| .matmulP _ => "matmulP"
| .reshapeP _ => "reshapeP"
| .identityP _ => "identityP"
| .transposeP _ => "transposeP"

/- The list of scalars used by an operator -/
def scalarDependencies : Operator Tensor Scalar -> List Scalar
| .dropout ⟨_, _, _, threshold⟩ => [threshold]
| .activate ⟨_, _, _, _, scale, bias, imm⟩ => [scale, bias, imm]
| .scalarTensorTensor ⟨_, _, _, _, _, _, imm0, _⟩ => [imm0]
| .tensorScalar ⟨_, _, imm0, _, imm1, _, _⟩ => [imm0, imm1]
| .tensorTensorScan ⟨_, _, _, _, _, _, imm0, _⟩ => [imm0]
| .rangeSelect ⟨_, _, _, _, _, _, _, _, bound0, bound1⟩ => [bound0, bound1]
| .matchReplace8 ⟨_, _, replaceValue⟩ => [replaceValue]
| .memSet ⟨_, value, _⟩ => [value]
| _ => []
