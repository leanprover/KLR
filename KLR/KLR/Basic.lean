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

import Init.Data.Int.Basic
import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util

namespace KLR.KLR
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

-- Compute Engines
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, Repr

-- Memory types
inductive Memory where
  | hbm | sbuf | pmem
  deriving Repr, BEq

/-
Tensor element types supported by HW and available from NKI.

The HW always performs operations on 32-bit types. However, when reading from
or writing to memory, automatic conversion to and from the following types is
supported.
-/
inductive Dtype where
  | bfloat16
  | float8e3 | float8e4 | float8e5
  | float16 | float32 | float32r
  | int8 | int16 | int64 | int32
  | uint8 | uint16 | uint32 | uint64
  with
    @[computed_field]
    size : Dtype -> Nat
    | .uint8 | .int8 | .float8e3 | .float8e4 | .float8e5 => 1
    | .uint16 | .int16 | .bfloat16 | .float16 => 2
    | .uint32 | .int32 | .float32 | .float32r => 4
    | .uint64 | .int64 => 8
    @[computed_field]
    isInt : Dtype -> Bool
    | .int8 | .int16 | .int64 | .int32
    | .uint8 | .uint16 | .uint32 | .uint64 => true
    | _ => false

  deriving Repr, BEq

/-
A tensor in HBM. The address is an offset into HBM.
-/
structure Tensor where
  dtype   : Dtype
  address : Nat
  shape   : TensorLib.Shape
  strides : List Nat
deriving BEq, Repr

/--
Access pattern elements.

These are used for HW-native indexing which consists of an offset and a list of
access pattern pairs. Each pair specifies a step size and the number of steps
to take. The first changes the slowest, and the last pair changes the fastest.
For example, in the list of pairs:

  [ (3,2), (1,3) ]

the first pair will produce the values 0,3 and the second pair will produce the
values 0,1,2. Added together, the pairs produce the values:

  0, 1, 2, 3, 4, 5.

which is equivalent to the basic index [0:2,0:3] for a standard tensor layout.
-/
structure APPair where
  step : Int := 1
  size : Nat := 1
deriving Repr, BEq

structure Reg where
  -- register number
  number : Nat
deriving BEq, Repr

inductive Immediate where
  | register (reg : Reg)
  | pointer -- TODO
  | int (i : Int32)
  | float (f : Float32)
deriving BEq, Repr

inductive ActivationImm where
  | register (reg : Reg)
  | pointer -- : TODO
  | float (f : Float32)
deriving BEq, Repr

inductive parQuadrant where
  | par0 | par32 | par64 | par96
  deriving Repr, BEq

/- A struct representing the layout of a tensor in the SBUF. This maps very
closely to the way that the ISA expects tensor accesses to be expressed.
Specifically, it separates the parallel dimension from the rest of the dimensions
and includes constraints like the fact that the parallel dimension stride is always 1.

              0┌──────────────────────┐
               │                      │
             32│                      │
               │                      │
             64│                      │
               │                      │
parQuadrant─►96│    ┌───────┐│        │
               │    └───────┘│parSize │
               └──────────────────────┘
                    ▲
                    │
               parOffset
-/
structure TensorView where
    /- Which parallel dimension channel this tensor starts at -/
    (parQuadrant : Nat)
    /- The size of this tensor in the parallel dimension -/
    (parSize : Nat)
    /- The offset in the partition channel of this tensor -/
    (parOffset : Nat := 0)
    /- The length and stride of each dimension besides the first, whose length
    is reprented by `parNum` above and whose stride is always 1 -/
    (freePattern: List APPair)
    (dtype : Dtype)

/-
The type that is passed to instructions to refer to a tensor in SBUF. We abstract
over whether the tensor is a literal or stored in a shape register.
-/
inductive TensorRef where
  /- A shape can be a literal -/
  | literal (_ : TensorView)
  /- A shape can be stored in a shape register -/
  | reg (_ : Reg)

/-
Used for Iota and AffineSelect, represents something similar to an
TensorView but that is only used to generate data, not to index. Much like
LEA in x86.
-/
structure DataPattern where
  offset  : Nat
  pattern  : List APPair
  channelMultiplier : Int
