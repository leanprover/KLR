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
import KLR.Trace.Types
import KLR.Trace.Tensor
import KLR.Trace.NKI

/-
# Basic tracing facilities

Basic tracing definitions only deal with Terms (not Python sources)
-/

namespace KLR.Core.Value

-- Python-like rules for conversion to boolean
def isTrue : Value -> Bool
  | .var _    => true
  | .bool b   => b
  | .int i    => i != 0
  | .float f  => f != 0.0
  | .access _ => true

-- Python-like rules for conversion to integer
/-
def toInt : Const -> Err Int
  | .none       => throw "none cannot be converted to an integer"
  | .bool true  => return 1
  | .bool false => return 0
  | .int i      => return i
  | .float f    =>
      -- Python is a bit strange here, it truncates both
      -- positive and negative numbers toward zero
      if f < 0.0 then
        return (Int.ofNat (Float.floor (-f)).toUInt64.toNat).neg
      else
        return Int.ofNat (Float.floor f).toUInt64.toNat
  | .string s   =>
      -- Fortunately, Lean's String.toInt appears to be compatible
      -- with Python's int(string) conversion.
      match s.toInt? with
      | .none  => throw s!"string {s} cannot be converted to an integer"
      | .some i => return i
-/
end KLR.Core.Value

namespace KLR.Trace
open Core

-- Truthiness of Terms following Python

def Term.isTrue : Term -> Err Bool
  | .none
  | .tuple []
  | .list []  => return false
  | .module _
  | .mgrid
  | .builtin ..
  | .source _
  | .string _
  | .tuple _
  | .list _
  | .ellipsis
  | .slice ..
  | .store ..
  | .pointer .. => return true
  | .expr (.value v) _ => return v.isTrue
  | .tensor _ =>
      -- Using ndarray as bool in Python raises:
      -- "ValueError: The truth value of an array with more than one element
      --  is ambiguous. Use a.any() or a.all()"
      throw "tensor cannot be evaluated as bool"
  | .expr _ _ => throw "non-constant expression"
  | .oper _ => throw "non constant expression"

def Term.isFalse (t : Term) : Err Bool :=
  return not (<- t.isTrue)

-- Following Python semantics, boolean operators return
-- the first value that is convertible to True or False

def boolOp (op : BoolOp) (es : List Term) : Err Term := do
  bop (<- bopFn op) es
where
  bop fn : List Term -> Err Term
    | []  => throw "invalid expression"
    | [x] => return x
    | x :: xs => do if (<- fn x) then return x else bop fn xs
  bopFn : BoolOp -> Err (Term -> Err Bool)
    | .lor  => return Term.isTrue
    | .land => return Term.isFalse

-- Binary Operators

-- Multiply a sequence (tuple, list, string) by a scalar
-- It is tempting to use Const.toInt here, but that would be
-- more permissive than Python. The only allowed cases are:
--   [1,2] * 2     => [1,2,1,2]
--   [1,2] * 0     => []
--   [1,2] * -10   => []
--   [1,2] * True  => [1,2]
--   [1,2] * False => []

private def mulseq (l : List a) : Value -> Err (List a)
  | .bool false => return []
  | .bool true  => return l
  | .int i      => return List.flatten $ List.replicate i.toNat l
  | _           => throw "invalid multiply"

-- Binary operators on constants
-- Note: both Lean and Python use big integers
-- TODO: imcomplete
private def valueOp : BinOp -> Value -> Value -> Trace Term
  -- tensors
  | op, .access l, .access r => tensor_tensor op l r
  | op, .access t, v => tensor_scalar op t v
  | op, v, .access t => scalar_tensor op v t
  -- constants
  | .add, .int l, .int r => return int (l + r)
  | .sub, .int l, .int r => return int (l - r)
  | .mul, .int l, .int r => return int (l * r)
  | .div, .int l, .int r => return int (l / r)
  | .mod, .int l, .int r => return int (l % r)
  | .floor, .int l, .int r =>
    if r = 0 then throw "division by zero" else
    let samesgn := (l < 0) ↔ (r < 0)
    let (l,r) := (l.natAbs, r.natAbs)
    let d := Int.ofNat (l / r)
    return int (
      if l % r = 0 then (if samesgn then id else Int.neg) d
      else (if samesgn then d else Int.neg (d + 1)))
  | _,_,_ => throw "unimp"
where
  int (i : Int) : Term := .expr (.value (.int i)) .int

-- Binary operators on tensors (see Tensor.lean)
private def exprOp : BinOp -> Expr -> Expr -> Trace Term
  | op, .value l, .value r => valueOp op l r
  | _ , _       , _        => throw "non-constant expression"

-- Binary operators on terms
-- TODO mulseq on strings
def binOp : BinOp -> Term -> Term -> Trace Term
  -- lists and tuples
  | .add, .string l,          .string r => return .string (l ++ r)
  | .add, .list   l,          .list   r => return .list (l ++ r)
  | .add, .tuple  l,          .tuple  r => return .tuple (l ++ r)
  | .mul, .list   l,          .expr (.value  v) _
  | .mul, .expr (.value v) _, .list l   => return .list (<- mulseq l v)
  | .mul, .tuple  l,          .expr (.value  v) _
  | .mul, .expr (.value v) _, .tuple l  => return .tuple (<- mulseq l v)
  -- expressions
  | op, .expr l _, .expr r _ => exprOp op l r
  | _, _, _ => throw "unsupported operator"

-- Unary operators
def unOp : UnaryOp -> Term -> Trace Term
  | op, .expr (.value $ .access t) _ => tensor_op op t
  | .not, t => return .expr (.value $ .bool (<- t.isFalse)) .bool
  | _, _ => throw "unsupported operator"

/-
Comparison operators

These functions implement the Python comparison operators. For tensors, these
will be promoted to per-element operations, for everything else the should be
static. For example:

  # comparison of two lists containing integer constants
  assert a_input.shape == b_input.shape

  # comparison of two integer constants
  assert a_input.shape[0] <= nl.tile_size.pmax

We only need Eq (==) and Lt (<), other operators are implemted in terms of
these two.
-/

private def exprEq : Expr -> Expr -> Trace Bool
  | .value l, .value r => return l == r
  | _, _ => return false

private def termEq : Term -> Term -> Trace Bool
  | .module m₁, .module m₂ => return m₁ == m₂
  | .builtin n₁ .., .builtin n₂ .. => return n₁ == n₂
  | .none, .none => return true
  | .string s₁, .string s₂ => return s₁ == s₂
  | .tuple l₁, .tuple l₂
  | .list  l₁, .list  l₂ => teq l₁ l₂
  | .ellipsis, .ellipsis => return true
  | .expr e₁ _, .expr e₂ _ => exprEq e₁ e₂
  | _, _ => return false
where
  teq : List Term -> List Term -> Trace Bool
    | [], [] => return true
    | x :: xs, y :: ys => return (<- termEq x y) && (<- teq xs ys)
    | _, _ => return false

-- Python "is" operator is the same as == for all literals, except for lists.
private def termIsIdentical : Term -> Term -> Trace Bool
  | .list _, .list _ => return false
  | l, r => termEq l r

-- Python: contains operator: 1 in [1,2,3]
-- TODO: strings
private def termIn (x : Term) : Term -> Trace Bool
  | .tuple l | .list l => l.anyM (termEq x)
  | _ => throw "invalid use of in"

private def valueLt : Value -> Value -> Trace Bool
  -- comparison between same types
  | .bool b₁, .bool b₂ => return !b₁ && b₂
  | .int l, .int r => return l < r
  | .float l, .float r => return l < r
  -- float promotion
  | .float f, .bool b => return f < if b then 1.0 else 0.0
  | .bool b, .float f => return (if b then 1.0 else 0.0) < f
  | .float f, .int i => return f < .ofInt i
  | .int i, .float f => return .ofInt i < f
  -- int promotion
  | .bool b, .int i => return (if b then 1 else 0) < i
  | .int i, .bool b => return i < (if b then 1 else 0)
  -- errors
  | _, _ => throw "unsupported comparison"

private def termLt : Term -> Term -> Trace Bool
  | .string l, .string r => return l < r
  | .tuple l, .tuple r
  | .list  l, .list  r => listLt l r
  | .expr (.value l) _, .expr (.value r) _ => valueLt l r
  | _, _ => throw "unsupported comparison"
where
  listLt : List Term -> List Term -> Trace Bool
  | [], [] => return false
  | [], _ => return true
  | _, [] => return false
  | x :: xs, y :: ys => do
      if <- termLt x y then return true
      else return (<- termEq x y) && (<- listLt xs ys)

def cmpOp : CmpOp -> Term -> Term -> Trace Bool
  | .eq, l, r => termEq l r
  | .ne, l, r => return not (<- termEq l r)
  | .lt, l, r => termLt l r
  | .le, l, r => return (<- termEq l r) || (<- termLt l r)
  | .gt, l, r => return not (<- termEq l r) && not (<- termLt l r)
  | .ge, l, r => return not (<- termLt l r)
  | .is, l, r => termIsIdentical l r
  | .isNot, l, r => return not (<- termIsIdentical l r)
  | .isIn, l, r => termIn l r
  | .notIn, l, r => return not (<- termIn l r)

-- Python comparison chains are short-circuting
-- e.g. x < y < z  => x < y && y < z
def compare : Term -> List CmpOp -> List Term -> Trace Term
  | x, [op], [y] => return bool (<- cmpOp op x y)
  | x, op::ops, y::ys => do
     if (<- cmpOp op x y)
     then compare y ops ys
     else return (bool false)
  | _, _, _ => throw "invalid comparison"
where
  bool b := .expr (.value $ .bool b) .bool

-- Attributes

def Term.attr : Term -> String -> Trace Term
  | .module n, id => lookup (n.str id)
  | .pointer addr, "start" => return tuple [addr.parOffset, addr.freeOffset]
  | .pointer addr, "size" => return tuple [addr.parSize, addr.freeSize]
  | .pointer addr, "view" => return memViewBuiltin addr
  | .expr _ (.tensor d _), "dtype" => return (dtype d)
  | .expr _ (.tensor _ s), "shape" => return (tuple $ s.toList.map some)
  | .expr _ (.obj n), id => lookup (n.str id)
  | _, id => throw s!"unsupported attribute {id}"
where
  dtype dty :=
    let name := "nki.language." ++ dstr dty
    .expr (.value $ .var name) (.obj name.toName)
  tuple (l : List (Option Nat)) : Term :=
    Term.tuple $ l.map fun
      | Option.none => Term.none
      | some x => .expr (.value (.int x)) .int
  dstr dty :=
    let s := reprStr dty
    match s.toName with
    | .str _ s => s
    | _ => panic! "internal error (dtype name)"

-- Static environment of builtins (extend as necessary)

nki memView (self : Address) (dtype : Dtype) (shape : Shape) (name : String := "tensor") := do
  let name := (<- genName (.mkStr1 name)).toString
  if parWF: shape.parDim <= self.parSize then
    if freeWF: shape.freeElements * dtype.size <= self.freeSize then
      let tensor := ⟨ name, dtype, shape, self, shape.freeElements, parWF, freeWF ⟩
      let ty := TermType.tensor dtype shape
      return .expr (.value (.access (.simple tensor))) ty
    else throw "shape is too large for memory region"
  else throw "partition size is too large for memory region"

def builtinEnv : List (Name × BuiltinFn) :=
  (memViewName, memView) ::
  NKIBuiltins

def builtinFn (name : Name) : Trace BuiltinFn :=
  match builtinEnv.lookup name with
  | some f => return f
  | none => throw s!"unimplemented API {name}"
