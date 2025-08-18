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

def QualifiedIdent.toString : QualifiedIdent → String
  | ([], i) => i
  | (qs, i) => s!"{".".intercalate qs}.{i}"

instance instToStringQualifiedIdent : ToString QualifiedIdent where
  toString := QualifiedIdent.toString

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
deriving BEq, ToJson, Inhabited

mutual

structure Arg where
  keyword : Option Ident := none
  val : Exp
deriving ToJson

inductive Index
  | coord (i : Exp)
  | slice (l u step : Option Exp)

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
  | call (f : Exp) (typArgs : List Exp) (args : List Arg)
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
  typ : Option Exp
  dflt : Option Exp
deriving ToJson

mutual

structure FuncDef where
  name : Ident
  typParams : List Ident
  params : List Param
  returns : Option Exp
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
  | assign (lhs : Exp) (typ : Option Exp) (rhs : Exp)
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
