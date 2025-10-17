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
import KLR.Trace.ISA

namespace KLR.Trace
open Core

def iterUnOp (t : TensorLib.Tensor) (f : ByteArray -> ByteArray) : Trace TensorLib.Tensor := do
  let mut dst := ByteArray.emptyWithCapacity t.data.size
  let dt := t.dtype
  for idx in t.shape.belist do
    let v := <- t.getDimIndex idx
    let v := f v
    dst := dst.append v
  return {dtype := dt, shape := t.shape, data := dst}

def iterBinOp (l r : TensorLib.Tensor) (f : ByteArray -> ByteArray -> ByteArray) : Trace TensorLib.Tensor := do
  if l.shape != r.shape then throw s!"tensors have different shapes {l.shape} {r.shape}"
  let mut dst := ByteArray.emptyWithCapacity l.data.size
  let dt := l.dtype
  for idx in l.shape.belist do
    let vl := <- l.getDimIndex idx
    let vr := <- r.getDimIndex idx
    let v := f vl vr
    dst := dst.append v
  return {dtype := dt, shape := l.shape, data := dst}

def tensorScalarOpByteArray (op : BinOp) (l : TensorLib.Tensor) (r : ByteArray) : Trace Term := do
  let dt := l.dtype
  match op with
  | .add => return .tensor $ <- iterUnOp l (fun x => dt.add! x r)
  | .sub => return .tensor $ <- iterUnOp l (fun x => dt.sub! x r)
  | .mul => return .tensor $ <- iterUnOp l (fun x => dt.mul! x r)
  | .div => return .tensor $ <- iterUnOp l (fun x => dt.div! x r)
  | op => throw s!"tensors do not support scalar operator '{repr op}'"

def tensorOpScalarFloat (op : BinOp) (l : TensorLib.Tensor) (r : Float) : Trace Term := do
  let dt := l.dtype
  let br := <- dt.byteArrayOfFloat32 r.toFloat32
  tensorScalarOpByteArray op l br

def tensorOpScalarInt (op : BinOp) (l : TensorLib.Tensor) (r : Int) : Trace Term := do
  let dt := l.dtype
  let br := <- dt.byteArrayOfInt r
  tensorScalarOpByteArray op l br

nki builtin.lang.transpose (src : Access) := do
  warn "transpose is not supported"
  return .access src

nki builtin.lang.zeros (shape: Shape) (dtype: Dtype) := do
  let tlShape := TensorLib.Shape.mk shape.toList
  let tlDtype <- dtype.toTensorLibDtype
  let tensor := TensorLib.Tensor.zeros tlDtype tlShape
  return .tensor tensor

nki builtin.lang.arange
 (start : Nat)
 (stop : Nat)
 (step : Nat := 1)
 (dtype : Dtype := .float32) := do
  let tlDtype <- dtype.toTensorLibDtype
  let cnt := (stop - start + step - 1).div  step
  let tlShape := TensorLib.Shape.mk [cnt]
  let values := List.range cnt |>.map (fun i => start + i * step)
  let mut data := ByteArray.emptyWithCapacity $ cnt * tlDtype.itemsize
  for v in values do
    let bytes <- tlDtype.byteArrayOfNat v
    data := data.append bytes
  return .tensor {dtype := tlDtype, shape := tlShape, data := data}

nki builtin.lang.identity
  (N : Nat)
  (dtype : Dtype := .float32) := do
  let tlDtype <- dtype.toTensorLibDtype
  let tlShape := TensorLib.Shape.mk [N, N]
  let mut data := ByteArray.emptyWithCapacity (N * N * tlDtype.itemsize)
  for i in [0:N] do
      for j in [0:N] do
        let value : Nat := if i == j then 1 else 0
        let bytes <- tlDtype.byteArrayOfNat value
        data := data.append bytes
  return .tensor { dtype := tlDtype, shape := tlShape, data := data }

nki builtin.lang.shared_constant
  (t : TensorLib.Tensor) := do
  let name <- genName
  let dtype <- Dtype.fromTensorLibDtype t.dtype
  let shape := Shape.mk t.shape.val.head! t.shape.val.tail!
  let (parSize, freeSize) := Address.defaultSize shape dtype
  let addr : Address := {
    name := name.toString,
    memory := .hbm,
    parSize := parSize,
    freeSize := freeSize
    isShared := true
  }
  let tensorName <- TensorName.make name.toString dtype shape addr

  modify fun s => { s with
    sharedConstants := s.sharedConstants.push (name.toString, t)
  }
  return .access (.simple tensorName)
