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
import KLR.Py.Util

def KLR.Core.Dtype.toString : Dtype → String
  | .bfloat16 => "bfloat16"
  | .float8e3 => "float8e3"
  | .float8e4 => "float8e4"
  | .float8e5 => "float8e5"
  | .float16 => "float16"
  | .float32 => "float32"
  | .float32r => "float32r"
  | .int8 => "int8"
  | .int16 => "int16"
  | .int64 => "int64"
  | .int32 => "int32"
  | .uint8 => "uint8"
  | .uint16 => "uint16"
  | .uint32 => "uint32"
  | .uint64 => "uint64"
  | .float8_e4m3 => "float8_e4m3"
  | .float8_e4m3fn => "float8_e4m3fn"
  | .float8_e5m2_x4 => "float8_e5m2_x4"
  | .float8_e4m3fn_x4 => "float8_e4m3fn_x4"
  | .float4_e2m1fn_x4 => "float4_e2m1fn_x4"

namespace KLR.Py

open KLR.Core (Dtype)
open Lean (ToJson)

abbrev Ident := String

abbrev QualifiedIdent := (List Ident × Ident)

def QualifiedIdent.toString : QualifiedIdent → String
  | ([], i) => i
  | (qs, i) => s!"{".".intercalate qs}.{i}"

instance instToStringQualifiedIdent : ToString QualifiedIdent where
  toString := QualifiedIdent.toString

inductive Numeric
  | int
  | float
deriving BEq, ToJson

inductive Prim
  | none
  | bool
  | numeric (numeric : Numeric)
  | string
  | dtype (dt : Dtype)
deriving BEq, ToJson

mutual

inductive Typ'
  | var (var : Ident)
  | forall (names : List Ident) (body : Typ)
  | prim (p : Prim)
  | func (params : List Typ) (ret : Typ)
  | size (n : Nat)
  | shape (dims : List Typ)
  | tuple (typs : List Typ)
  | list (typ : Typ)
  | tensor (shape : Typ) (dt : Typ)
  | iter (typ : Typ)
  | sizeAdd (x y : Typ)
  | shapeAppend (s1 s2 : Typ)
deriving ToJson

structure Typ where
  span : Span
  typ  : Typ'
deriving ToJson

end

inductive Value
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | ellipsis
deriving ToJson

inductive UnaryOp
  | pos | neg | bitwiseNot | lnot
deriving ToJson, Inhabited

inductive BinOp
  -- logical
  | land | lor
  -- bitwise
  | bitwiseOr | bitwiseXor | bitwiseAnd | lshift | rshift
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub
  | mul | div
  | mod | pow
  | floor
  -- other
  | matmul
deriving BEq, ToJson, Inhabited, Repr

mutual

structure Arg where
  keyword : Option Ident := none
  val : Exp
deriving ToJson

inductive Index
  | coord (i : Exp)
  | slice (l u step : Option Exp)
  | dynamic (t l u : Exp)

structure Exp where
  span : Span := {}
  exp  : Exp'
deriving ToJson

inductive Exp'
  | var (name : Ident)
  | value (value : Value)
  | unaryOp (op : UnaryOp) (x : Exp)
  | binOp (op : BinOp) (x y : Exp)
  | tuple (es : List Exp)
  | list (es : List Exp)
  | ifExp (test body orelse : Exp)
  | call (f : Exp) (typArgs : List Typ) (args : List Arg)
  | access (e : Exp) (indices : List Index)
  | attr (e : Exp) (field : Ident)
deriving ToJson

end

instance : Inhabited Exp := ⟨{ exp := .value .none }⟩

inductive Pattern
  | var (name : Ident)
  | tuple (pats : List Pattern)
deriving ToJson

structure Param where
  name : Ident
  typ : Option Typ
  dflt : Option Exp
deriving ToJson

mutual

structure FuncDef where
  name : Ident
  typParams : List Ident
  params : List Param
  returns : Option Typ
  body : List Stmt
  decorators : List Exp
  whereBounds : List Exp
deriving ToJson

structure Stmt where
  span : Span := {}
  stmt : Stmt'
deriving ToJson

inductive Stmt'
  | exp (exp : Exp)
  | imprt (mod : QualifiedIdent) (as : Option Ident)
  | imprtFrom (mod : QualifiedIdent) (imp : Ident) (as : Option Ident)
  | ret (e : Exp)
  | assign (lhs : Exp) (typ : Option Typ) (rhs : Exp)
  | assert (e : Exp)
  | funcDef (dfn : FuncDef)
  | ifStm (cond : Exp) (thn : List Stmt) (elifs : List (Exp × List Stmt)) (els : Option (List Stmt))
  | forLoop (pat : Pattern) (iter : Exp) (body : List Stmt)
  | whileLoop (cond : Exp) (body : List Stmt)
  | pass
  | breakLoop
  | continueLoop
deriving ToJson

end

structure Prog where
  file : String
  stmts : List Stmt
deriving ToJson
