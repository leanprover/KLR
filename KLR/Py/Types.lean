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

import KLR.Py.Util

namespace KLR.Py

open Lean (ToJson)

abbrev Ident := String

abbrev QualifiedIdent := (List Ident × Ident)

inductive Kind
  | size
  | shape
  | dtype
  | type
  | arrow (κ ι : Kind)
deriving ToJson

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

mutual

structure Typ where
  pos : Pos := {}
  typ : Typ'
deriving ToJson

inductive Typ'
  | var (name : Ident)
  | prim (p : Prim)
  | func (typParams : List Ident) (params : List Typ)
  | iter (e : Typ)
  | tuple (ts : List Typ)
  | list (t : Typ)
deriving ToJson

end

/-!
# Utilities
-/

def QualifiedIdent.toString : QualifiedIdent → String
  | ([], i) => i
  | (qs, i) => s!"{".".intercalate qs}.{i}"

instance instToStringQualifiedIdent : ToString QualifiedIdent where
  toString := QualifiedIdent.toString

scoped notation "⋆" => Kind.type
scoped infixr:55 " ⟶⋆ " => Kind.arrow

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

instance : Inhabited Typ where
  default := { typ := .prim .none }
