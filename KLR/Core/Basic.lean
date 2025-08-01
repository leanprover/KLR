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

/-!
# Abstract syntax of Core NKL language

This language is the result of "tracing", and is used as the
portable format, a.k.a. Kernel Language Representation (KLR).
-/
namespace KLR.Core
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

export Lean (Name)
deriving instance Ord for Name

/-
A source position records the location of a statement in the original program.
-/

@[serde tag = 100]
structure Pos where
  line : Nat := 0
  column : Nat := 0
  lineEnd : Option Nat := none
  columnEnd : Option Nat := none
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
Fully reduced values

While it may seem strange, an `Access` is really a value. It succinctly
describes an (admittedly complex) set of physical memory locations. However,
we only lookup or set the bits in those locations when applied to an operator.
-/
@[serde tag = 101]
inductive Value where
  | var (x : String)
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | access (a : Access)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/--
Expressions are trivial right now, waiting on dynamic loops.

The call expression would only appear in a KLR program if the tracer
encountered an unknown function.
-/
@[serde tag = 102]
structure Keyword where
  name : String
  value : Value
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 103]
inductive Expr where
  | value (v : Value)
  | call (f : String) (args : List Value) (kwargs : List Keyword)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 104]
inductive Stmt where
  | ret (v : Value)
  | assign (x : String) (e : Expr)
  | store (dst : Access) (op : Operator) (args : List Value)
  | oper (op : Operator)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 105]
structure Kernel where
  name : String
  inputs : List TensorName
  outputs : List TensorName
  body : List Stmt
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- Utilities

class Tensors (a : Type) where
  tensors : a -> List TensorName
export Tensors (tensors)

instance : Tensors TensorName where
  tensors tn := [tn]

-- TODO: not efficient
instance [Tensors a] : Tensors (List a) where
  tensors l := (l.flatMap tensors).eraseDups

instance : Tensors Access where
  tensors a := [a.tensor]

instance : Tensors Value where
  tensors
  | .access a => tensors a
  | _ => []

instance : Tensors Expr where
  tensors
  | .value v => tensors v
  | .call _ args kwargs => tensors (args ++ kwargs.map fun kw => kw.value)

instance : Tensors TensorRef where
  tensors
  | .abstract a => tensors a
  | .sbuf _ => []
  | .psum _ => []
  | .hbm _ => []
  | .register _ => []

instance : Tensors Operator where
  tensors op :=
    let refs := match op with
      | .activate d => [d.dst, d.src]
      | .affineSelect a => [a.dst, a.src]
      | .dmaCopy d => [d.dst, d.src]
      | .dmaTranspose d => [d.dst, d.src]
      | .dropout d => [d.dst, d.src]
      | .iota i => [i.dst]
      | .loadMaskRegister _ => []
      | .loadStationary l => [l.src]
      | .localGather l => [l.dst, l.src]
      | .matMul m => [m.dst, m.moving]
      | .memSet m => [m.dst]
      | .rangeSelect r => [r.dst, r.src]
      | .shuffle s => [s.dst, s.src]
      | .tensorReduce r => [r.dst, r.src]
      | .tensorTensorScan t => [t.dst, t.src0, t.src1]
      | .scalarTensorTensor s => [s.dst, s.src0, s.src1]
      | .transpose t => [t.dst, t.src]
      | .copy c => [c.dst, c.src]
      | .copyPredicated c => [c.dst, c.src, c.predicate]
      | .batchNormAggregate b => [b.dst, b.src]
      | .batchNormStats b => [b.dst, b.src]
      | .findIndex8 f => [f.dst, f.src]
      | .matchReplace8 m => [m.dst, m.src]
      | .matchValueLoad m => [m.src]
      | .max8 m => [m.dst, m.src]
      | .reciprocal r => [r.dst, r.src]
      | .tensorScalar t => [t.dst, t.src]
      | .tensorTensor t => [t.dst, t.src0, t.src1]
      | .ncMatMul t => [t.dst, t.stationary, t.moving]
    refs.flatMap tensors

instance : Tensors Stmt where
  tensors
  | .ret v => tensors v
  | .assign _ e => tensors e
  | .store dst _ vs => tensors (tensors dst :: vs.map tensors)
  | .oper op => tensors op

def Kernel.internal (k : Kernel) : List TensorName :=
  let ts := (k.body.map tensors).flatten.eraseDups
  (ts.removeAll (tensors k.inputs)).removeAll (tensors k.outputs)
