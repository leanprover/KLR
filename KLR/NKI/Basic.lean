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

export Core (Name Pos Edges)

-- Note: the python int and float types are compatible with Lean's types
-- The str type may require conversion (to UTF8).
@[serde tag = 1]
inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | tensor (shape : List Nat) (dtype : String) (name : Option String)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- Note: land, lor do not short-circuit (see conj, disj below)
@[serde tag = 2]
enum BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving FromCBOR, ToCBOR

mutual
@[serde tag = 3]
structure Expr where
  expr : Expr'
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- Note: conj and disj are short-circuit operators
@[serde tag = 4]
inductive Expr' where
  | value (value : Value)
  | var (name : Name)
  | tuple (elements : List Expr)
  | list (elements : List Expr)
  | dict (elements : List Keyword)
  | access (expr : Expr) (indices : List Index)
  | binOp (op : BinOp) (left right : Expr)
  | conj (left right : Expr)
  | disj (left right : Expr)
  | ifExp (test tru fls : Expr)
  | call (f: Expr) (args: List Expr) (keywords : List Keyword)
  | object (cls : Name) (fields : List Keyword)
  | format (expr : Expr) (repr : Bool)
  | joined (es : List Expr)
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

namespace Pattern

def isVar : Pattern -> Bool
  | .var .. => true | _ => false

end Pattern

@[serde tag = 8]
enum RangeType where
  | static
  | affine
  | sequential
  | dynamic
  deriving FromCBOR, ToCBOR

@[serde tag = 9]
inductive Iterator where
  | expr (e : Expr)
  | range (ty : RangeType) (l u s : Expr)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

mutual
@[serde tag = 10]
structure Stmt where
  stmt : Stmt'
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 11]
inductive Stmt' where
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e : Expr)
  | declare (x : Name) (ty : Expr)
  | letM (p : Pattern) (ty : Option Expr) (e : Expr)
  | setM (x e : Expr) (accum : Bool)
  | ifStm (e : Expr) (thn els: List Stmt)
  | forLoop (x : Name) (iter: Iterator) (body: List Stmt)
  | breakLoop
  | continueLoop
  | whileLoop (test : Expr) (body: List Stmt)
  | dynWhile (tensor : Expr) (body : List Stmt)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
end

@[serde tag = 12]
structure Param where
  name : String
  dflt : Option Expr
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 13]
structure Fun where
  name : Name
  decs : List Name := []
  file : String := "<unknown file>"
  line : Nat := 0
  source : String := "<source unavailable>"
  body : List Stmt := []
  args : List Param := []
  deriving FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- Names are fully qualified and unique
instance : BEq Fun where
  beq l r := l.name == r.name

@[serde tag = 14]
structure Class where
  name : Name
  bases : List Name
  decs : List Name
  fields : List Keyword
  methods : List Fun
  deriving FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

-- Names are fully qualified and unique
instance : BEq Class where
  beq l r := l.name == r.name

@[serde tag = 15]
structure Arg where
  name : String
  value : Expr
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 16]
structure Kernel where
  entry : Name
  funs : List Fun
  cls : List Class
  args : List Arg
  globals : List Arg
  grid : Nat
  edges : List Edges
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
