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
import KLR.NKI.Typed.Common

namespace KLR.NKI.Typed.Python

open KLR.Core (Pos)
open Lean (ToJson)

/-!
# Python IR

High-level IR for NKI that closely resembles the python AST
-/

abbrev Ident := String

abbrev QualifiedIdent := (List Ident × Ident)

def QualifiedIdent.toString : QualifiedIdent → String
  | ([], i) => i
  | (qs, i) => s!"{".".intercalate qs}.{i}"

instance instToStringQualifiedIdent : ToString QualifiedIdent where
  toString := QualifiedIdent.toString

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

instance : Inhabited Typ where
  default := { typ := .prim .none }

inductive Value
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | tensor (value : TensorLib.Tensor)
deriving ToJson

inductive UnaryOp
  | neg
deriving ToJson

inductive BinOp
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub
  | mul | div
  | mod | pow
  | floor
deriving BEq, ToJson

mutual

structure Arg where
  keyword : Option Ident
  val : Exp
deriving ToJson

inductive Index
  | coord (i : Exp)
  | slice (l u step : Option Exp)
  | ellipsis

structure Exp where
  pos : Pos := {}
  exp : Exp'
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
  pos : Pos
  name : Ident
  typParams : List Ident
  params : List Param
  returns : Option Typ
  body : List Stmt
  decorators : List Exp
deriving ToJson

structure Stmt where
  pos : Pos := {}
  stmt : Stmt'
deriving ToJson

inductive Stmt'
  | exp (exp : Exp)
  | imprt (mod : QualifiedIdent) (as : Option Ident)
  | imprtFrom (mod : QualifiedIdent) (imp : Ident) (as : Option Ident)
  | ret (e : Exp)
  | assign (pat : Pattern) (typ : Option Typ) (rhs : Exp)
  | funcDef (dfn : FuncDef)
  | ifStm (cond : Exp) (thn : List Stmt) (elifs : List (Exp × List Stmt)) (els : Option (List Stmt))
  | forLoop (name : Ident) (iter : Exp) (body : List Stmt)
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

/-!
# -----------------------------Pretty Printer-----------------------------------
-/
