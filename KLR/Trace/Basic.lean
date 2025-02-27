/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Tensor
import KLR.Trace.NKI

/-
# Basic tracing facilities

Basic tracing definitions only deal with Terms (not Python sources)
-/

namespace KLR.Core.Const

-- Python-like rules for conversion to boolean
def isTrue : Const -> Bool
  | .none     => false
  | .bool b   => b
  | .int i    => i != 0
  | .float f  => f != 0.0
  | .string s => s != ""

-- Python-like rules for conversion to integer
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

end KLR.Core.Const

namespace KLR.Trace
open KLR.Core

-- Operators within index expressions

def indexBinOp : String -> IndexExpr -> IndexExpr -> Err IndexExpr
  | "Add" ,      l,      r => return .add l r
  | "Sub" ,      l,      r => return .add l r.neg
  | "Mult", .int i,      e
  | "Mult",      e, .int i => return .mul i e
  | "Div" ,      e, .int i => return .floor e i
  | "Mod" ,      e, .int i => return .mod e i
  | _, _, _ => throw "invalid index expression"

def indexUnOp : String -> IndexExpr -> Err IndexExpr
  | "USub", e => return .neg e
  | _, _ => throw "invalid index expresssion"

-- Truthiness of Terms following Python

def Term.isTrue : Term -> Err Bool
  | .tuple []
  | .list []  => return false
  | .module _
  | .builtin ..
  | .source _
  | .tuple _
  | .list _
  | .ellipsis
  | .slice ..
  | .store .. => return true
  | .expr (.const c) _ => return c.isTrue
  | .expr _ _ => throw "non-constant expression"

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
    | .or  => return Term.isTrue
    | .and => return Term.isFalse

-- Binary Operators

-- Multiply a sequence (tuple, list, string) by a scalar
-- It is tempting to use Const.toInt here, but that would be
-- more permissive than Python. The only allowed cases are:
--   [1,2] * 2     => [1,2,1,2]
--   [1,2] * 0     => []
--   [1,2] * -10   => []
--   [1,2] * True  => [1,2]
--   [1,2] * False => []

private def mulseq (l : List a) : Const -> Err (List a)
  | .bool false => return []
  | .bool true  => return l
  | .int i      => return List.flatten $ List.replicate i.toNat l
  | _           => throw "invalid multiply"

-- Binary operators on constants
-- Note: both Lean and Python use big integers
private def constOp : BinOp -> Const -> Const -> Err Term
  | .add, .int l, .int r => return int (l + r)
  | .sub, .int l, .int r => return int (l - r)
  | .mul, .int l, .int r => return int (l * r)
  | .div, .int l, .int r => return int (l / r)
  | _,_,_ => throw "unimp"
where
  int (i : Int) : Term := .expr (.const (.int i)) .int

-- Binary operators on tensors (see Tensor.lean)
private def exprOp : BinOp -> Expr -> Expr -> Trace Term
  -- tensors
  | op, .tensor l, .tensor r => tensor_tensor op l r
  | op, .tensor t, .const  c => tensor_scalar op t c
  | op, .const  c, .tensor t => scalar_tensor op c t
  | _ , .tensor _, _
  | _ , _        , .tensor _ => throw "invalid tensor op"
  -- constants
  | op, .const  l, .const  r => constOp op l r
  | _ , _        , _         => throw "non-constant expression"

-- Binary operators on terms
def binOp : BinOp -> Term -> Term -> Trace Term
  -- lists and tuples
  | .add, .list   l,          .list   r => return .list (l ++ r)
  | .add, .tuple  l,          .tuple  r => return .tuple (l ++ r)
  | .mul, .list   l,          .expr (.const  c) _
  | .mul, .expr (.const c) _, .list l   => return .list (<- mulseq l c)
  | .mul, .tuple  l,          .expr (.const  c) _
  | .mul, .expr (.const c) _, .tuple l  => return .tuple (<- mulseq l c)
  -- expressions
  | op, .expr l _, .expr r _ => exprOp op l r
  | _, _, _ => throw "unsupported operator"

-- Unary operators
def unOp : UnaryOp -> Term -> Trace Term
  | op, .expr (.tensor t) _ => tensor_op op t
  | .not, t => return .expr (.const $ .bool (<- t.isFalse)) .bool
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
  | .var x, .var y => return x == y
  | .const c₁, .const c₂ => return c₁ == c₂
  | .tensor t₁, .tensor t₂ => return t₁.name == t₂.name
  | _, _ => return false

private def termEq : Term -> Term -> Trace Bool
  | .module m₁, .module m₂ => return m₁ == m₂
  | .builtin n₁ _, .builtin n₂ _ => return n₁ == n₂
  | .tuple l₁, .tuple l₂
  | .list  l₁, .list  l₂ => teq l₁ l₂
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
private def termIn (x : Term) : Term -> Trace Bool
  | .tuple l | .list l => l.anyM (termEq x)
  | _ => throw "invalid use of in"

private def constLt : Const -> Const -> Trace Bool
  -- comparison between same types
  | .bool b₁, .bool b₂ => return !b₁ && b₂
  | .int l, .int r => return l < r
  | .float l, .float r => return l < r
  | .string l, .string r => return l < r
  -- float promotion
  | .float f, .bool b => return f < if b then 1.0 else 0.0
  | .bool b, .float f => return (if b then 1.0 else 0.0) < f
  | .float f, .int i => return f < .ofInt i
  | .int i, .float f => return .ofInt i < f
  -- int promotion
  | c, .int i => return (<- c.toInt) < i
  | .int i, c => return i < (<- c.toInt)
  -- errors
  | .string _, _ | _, .string _ => throw "unsupported comparison"
  | .none, _ | _, .none => throw "unsupported comparison"

private def termLt : Term -> Term -> Trace Bool
  | .tuple l₁, .tuple l₂
  | .list  l₁, .list  l₂ => listLt l₁ l₂
  | .expr (.const c₁) _, .expr (.const c₂) _ => constLt c₁ c₂
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
-- e.g. x < y < z  => x < y || y < z
def compare : Term -> List CmpOp -> List Term -> Trace Term
  | x, [op], [y] => return bool (<- cmpOp op x y)
  | x, op::ops, y::ys => do
     if (<- cmpOp op x y)
     then compare y ops ys
     else return (bool false)
  | _, _, _ => throw "invalid comparison"
where
  bool b := .expr (.const $ .bool b) .bool

-- Attributes

def Term.attr : Term -> String -> Trace Term
  | .module n, id => lookup (n.str id)
  | .expr _ (.tensor d _), "dtype" => return (dtype d)
  | .expr _ (.tensor _ s), "shape" => return (tuple s)
  | _, id => throw s!"unsupported attribute {id}"
where
  dtype dty :=
    let name := "nki.language." ++ toString (Std.format dty)
    .expr (.var name) (.obj name.toName)
  tuple l := .tuple $ l.map fun i => .expr (.const (.int $ .ofNat i)) .int

-- Static environment of builtins (extend as necessary)

def builtinEnv : List (Name × Builtin.BuiltinFn) :=
  NKIBuiltins

def builtinFn (name : Name) : Trace Builtin.BuiltinFn :=
  match builtinEnv.lookup name with
  | some f => return f
  | none => throw s!"unimplemented API {name}"
