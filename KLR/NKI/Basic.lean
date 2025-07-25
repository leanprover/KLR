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
import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util
import KLR.Compile.Pass

/-!
# Abstract syntax of NKI functions

This AST is produced from the Python AST by simplification.
The two ASTs are similar. This one is the "official" abstract
syntax of NKI.
-/

namespace KLR.NKI
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)
open Compile.Pass(PassM freshName)

export Core (Name Pos)

-- Note: the python int and float types are compatible with Lean's types
-- The str type may require conversion (to UTF8).
@[serde tag = 1]
inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | tensor (shape : List Nat) (dtype : String)  -- TODO use Core Dtype
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 2]
inductive BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

mutual
@[serde tag = 3]
structure Expr where
  expr : Expr'
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 4]
inductive Expr' where
  | value (value : Value)
  | var (name : Name)
  | tuple (elements : List Expr)
  | access (expr : Expr) (indices : List Index)
  | binOp (op : BinOp) (left right : Expr)
  | ifExp (test body orelse : Expr)
  | call (f: Expr) (args: List Expr) (keywords : List Keyword)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 5]
inductive Index where
  | coord (i : Expr)
  | slice (l u step : Option Expr)
  | ellipsis
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 6]
structure Keyword where
  name : String
  expr : Expr
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
end

@[serde tag = 7]
inductive Pattern where
  | var (name : Name)
  | tuple (xs : List Pattern)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

def Pattern.isVar : Pattern -> Bool
  | .var .. => true | _ => false

def Pattern.findVar (ps : List Pattern) : PassM (Name × List Pattern) :=
  match ps.partition Pattern.isVar with
  | ([], ps) => return (<- freshName, ps)
  | (.var n :: vs, ps) => return (n, vs ++ ps)
  | _ => throw "invalid pattern"

mutual
@[serde tag = 8]
structure Stmt where
  stmt : Stmt'
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 9]
inductive Stmt' where
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e : Expr)
  | declare (x : Name) (ty : Expr)
  | letM (p : Pattern) (ty : Option Expr) (e : Expr)
  | setM (x e : Expr) (accum : Bool)
  | ifStm (e : Expr) (thn els: List Stmt)
  | forLoop (x : Expr) (iter: Expr) (body: List Stmt)
  | breakLoop
  | continueLoop
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
end

@[serde tag = 10]
structure Param where
  name : String
  dflt : Option Expr
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 11]
structure Fun where
  name : String
  file : String
  line : Nat
  body : List Stmt
  args : List Param
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 12]
structure Arg where
  name : String
  value : Expr
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 13]
structure Kernel where
  entry : String
  funs : List Fun
  args : List Arg
  globals : List Arg
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
