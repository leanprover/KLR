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

import TensorLib

open Lean (ToJson ToExpr)

deriving instance ToExpr for String.Pos
deriving instance ToJson for TensorLib.Dtype, String.Pos

/-- Dummy implementation for debugging use -/
instance instTojsonTensor : ToJson TensorLib.Tensor where
  toJson _ := .str "tensor"

def TensorLib.Dtype.toString : TensorLib.Dtype → String
  | .bool => "bool"
  | .int8 =>  "int8"
  | .int16 =>  "int16"
  | .int32 =>  "int32"
  | .int64 =>  "int64"
  | .uint8 =>  "uint8"
  | .uint16 =>  "uint16"
  | .uint32 =>  "uint32"
  | .uint64 =>  "uint64"
  | .float32 =>  "float32"
  | .float64 =>  "float64"

namespace KLR.NKI.Typed

inductive Kind
  | size
  | shape
  | dtype
  | type
  | arrow (κ ι : Kind)
deriving ToJson
scoped notation "⋆" => Kind.type
scoped infixr:55 " ⟶⋆ " => Kind.arrow

inductive Numeric
  | int
  | float
deriving ToJson

inductive Prim
  | none
  | bool
  | numeric (numeric : Numeric)
  | string
  | dtype (dt : TensorLib.Dtype)
deriving ToJson

def Numeric.toString : Numeric → String
  | .int => "int"
  | .float => "float"

instance instToStringNumeric : ToString Numeric where
  toString := Numeric.toString

instance instReprNumeric : Repr Numeric where
  reprPrec n _ := n.toString

abbrev Numeric.max : Numeric → Numeric → Numeric
  | .float, _ => .float
  | _, .float => .float
  | _, _ => .int

instance instMaxNumeric : Max Numeric where
  max := Numeric.max

def Prim.toString : Prim → String
  | none => "None"
  | bool => "bool"
  | numeric n => n.toString
  | string => "str"
  | dtype dt => dt.toString

instance instToStringPrim : ToString Prim where
  toString := Prim.toString

instance instReprPrim : Repr Prim where
  reprPrec p _ := p.toString
