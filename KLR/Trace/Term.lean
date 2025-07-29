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
import KLR.Trace.ISA
import KLR.Trace.Types
import KLR.Trace.Tensor

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
  | .mgItem ..
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
  | .expr _ _ => throw "non-constant expression"

def Term.isFalse (t : Term) : Err Bool :=
  return not (<- t.isTrue)

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
  | op,_,_ => throw s!"unimplemented operator {op}"
where
  int (i : Int) : Term := .expr (.value (.int i)) .int

-- Binary operators on tensors (see Tensor.lean)
private def exprOp : BinOp -> Expr -> Expr -> Trace Term
  | op, .value l, .value r => valueOp op l r
  | _ , _       , _        => throw "non-constant expression"

-- Binary operators on terms
-- TODO mulseq on strings
def termOp : BinOp -> Term -> Term -> Trace Term
  -- lists and tuples
  | .add, .string l,          .string r => return .string (l ++ r)
  | .add, .list   l,          .list   r => return .list (l ++ r)
  | .add, .tuple  l,          .tuple  r => return .tuple (l ++ r)
  | .mul, .list   l,          .expr (.value  v) _
  | .mul, .expr (.value v) _, .list l   => return .list (<- mulseq l v)
  | .mul, .tuple  l,          .expr (.value  v) _
  | .mul, .expr (.value v) _, .tuple l  => return .tuple (<- mulseq l v)
  -- mgrid
  | .add, .expr (.value (.int i)) _, .mgItem a b
  | .add, .mgItem a b, .expr (.value (.int i)) _ => return .mgItem (a+i) b
  -- expressions
  | op, .expr l _, .expr r _ => exprOp op l r
  | a, b, c => throw s!"unsupported operator {repr a} {repr b} {repr c}"

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

local instance : Coe Bool Term where
  coe b := .expr (.value $ .bool b) .bool

def binop (op : BinOp) (l r : Term) : Trace Term := do
  match op with
  -- logical
  | .land => return ((<- l.isTrue) && (<- r.isTrue))
  | .lor  => return ((<- l.isTrue) || (<- r.isTrue))
  -- comparison
  | .eq => termEq l r
  | .ne => return not (<- termEq l r)
  | .lt => termLt l r
  | .le => return (<- termEq l r) || (<- termLt l r)
  | .gt => return not (<- termEq l r) && not (<- termLt l r)
  | .ge => return not (<- termLt l r)
  -- arithmetic / bitwise
  | _ => termOp op l r


/-
# Evaluating index expressions

An index expression occurs only within a subscript expression. For example, in
the expression:

  t[1,1:10,None,x+9]

all of 1, 1:10, None, and x+9 are indexes. Note None may also be written as
np.newaxis. Also, a None or a slice (or ellipsis) may only occur at the
outer-most level of an index: if you write, e.g.

  t[x+None]

then the None is interpreted as an integer and not as a new axis. If you write,

  t[(1:2) + 3]
  t[... * 8]

these are syntax errors in python. Note, we do not support nested tuples or
lists as indexes e.g. t[1,(2,3),4] is disallowed
-/

-- Convert a shape and list of Terms to an list of Indexes (if possible)
def toIndex (shape : List Nat) (ts : List Term) : Err (List Core.Index) := do
  let slice (d : Nat) := (Core.Slice.make 0 d 1).map .slice
  match shape, ts with
  | [], []
  | [], [.ellipsis] => return []
  | [], _  => throw "too many indexes for shape"
  | ds, [] => ds.mapM slice
  | d :: ds, t :: ts =>
    match t with
    | .none => return (<- slice d) :: (<- toIndex ds ts)
    | .ellipsis =>
        if ds.length + 1 == ts.length
        then toIndex (d::ds) ts
        else return (<- slice d) :: (<- toIndex ds (t::ts))
    | .slice x y z => do
        let d := Int.ofNat d
        let x := x.getD 0
        let y := y.getD d
        let z := z.getD 1
        let x := if x < 0 then d + x else x
        let y := if y < 0 then d + y else y
        if x < 0 || x >= d || y < 0 || y > d || z <= 0 then
          throw "index out of range of tensor dimension"
        return .slice (<- Core.Slice.make x.toNat y.toNat z) :: (<- toIndex ds ts)
    | .tuple _ | .list  _ => throw "nested tuple/list indexes not supported"
    | .mgItem s e =>
        return .slice (<- Core.Slice.make s.toNat e.toNat 1) :: (<- toIndex ds ts)
    | t => do
        let i : Int <- fromNKI? t
        if i < 0 || i >= d then
          throw "index out of range of tensor dimension"
        return .coord i.toNat :: (<- toIndex ds ts)


-- Note, a list index can be negative, which means index from end of list.
-- Python also allows l[True] and l[False]
-- TODO: add case for slice
def listAccess (l : List Term) : List Term -> Err Term
  | [.expr (.value (.bool false)) _] => do
      if h:l.length > 0 then return l.get (Fin.mk 0 h)
      else throw "index out of bounds"
  | [.expr (.value (.bool true)) _] => do
      if h:l.length > 1 then return l.get (Fin.mk 1 h)
      else throw "index out of bounds"
  | [.expr (.value (.int i)) _] => do
      let i := if i < 0 then l.length + i else i
      if i < 0 then throw "index out of bounds"
      let n := i.toNat
      if h:l.length > n then return l.get (Fin.mk n h)
      else throw "index out of bounds"
  |_ => throw s!"index must be an integer or slice"

/-
Access to pointer types (a.k.a. Address)
NKI users can define memory regions by using slices on other memory regions.
Initially, the regions `sbuf` and `psum` are defined. For example:

  ptr = sbuf[0:32, 0:512]  # memory region in SBUF
  ptr2 = ptr[:, :256]      # left half of region
  ptr3 = ptr[:, 256:]      # right half of region

https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/nki_arch_guides.html
-/

def pointerAccess (addr : Core.Address) (i : List Term) : Err Term := do
  let chkPdim (p : Nat) : Err Nat := do
    if p != 0 && p != 32 && p != 64 && p != 96 then
      throw "partition dimension must be 0, 32, 64, or 96"
    if p > addr.parSize then
      throw s!"partition dimension {p} is larger than the pointer size {addr.parSize}"
    return p

  let chkFdim (f : Nat) : Err Nat := do
    if f < 0 then
      throw s!"free dimension {f} must be positive"
    if f % 2 != 0 then
      throw s!"free dimension {f} must be even"
    if f > addr.freeSize then
      throw s!"free dimension {f} is larger than pointer size {addr.freeSize}"
    return f

  let chkPslice (s : Core.Slice) : Err (Option Nat × Nat) := do
    if s.u < 0 then
      throw s!"partition size {s.u} must be positive"
    if s.u > addr.parSize then
      throw s!"partition size {s.u} is larger than the pointer size {addr.parSize}"
    if s.step != 1 then
      throw "pointer step size must be 1"
    let a <- chkPdim s.l
    if a >= s.u then
      throw s!"partition start {a} is larger than partition end {s.u}"
    return (a, s.u - a)

  let chkFslice (s : Core.Slice) : Err (Option Nat × Nat) := do
    let b <- chkFdim s.u
    if s.step != 1 then
      throw "pointer step size must be 1"
    if s.l < 0 then
      throw "free dimenstion start must be positive"
    if s.l % 2 != 0 then
      throw s!"free dimension start {s.l} must be even"
    if s.l >= b then
      throw s!"free start {s.l} is larger than free end {b}"
    return (s.l, b - s.l)

  let ptr (parOffset freeOffset : Option Nat) (size : Nat × Nat) : Term :=
    .pointer { memory := addr.memory
               parSize := size.1
               freeSize := size.2
               parOffset,
               freeOffset,
             }

  match <- toIndex [addr.parSize, addr.freeSize] i with
  | [.coord p, .coord f] => do
      let p <- chkPdim p
      let f <- chkFdim f
      return ptr p f (1, 1)

  | [.coord p, .slice s] => do
      let p <- chkPdim p
      let (start, size) <- chkFslice s
      return ptr p start (1, size)

  | [.slice s, .coord f] => do
      let (start, size) <- chkPslice s
      let f <- chkFdim f
      return ptr start f (size, 1)

  | [.slice s1, .slice s2] => do
      let (p0, p1) <- chkPslice s1
      let (f0, f1) <- chkFslice s2
      return ptr p0 f0 (p1, f1)

  | _ => throw "pointers require two indexes"

-- nl.mgrid
def mgrid (indexes : List Term) : Err Term := do
  let mut l := []
  for i in indexes do
    match i with
    | .slice a b c =>
      let a := a.getD 0
      if b == none then
        throw "size not specified"
      let b := b.get!
      if c != none && c != some 1 then
        throw "step size must be 1"
      l := l ++ [.mgItem a b]
    | _ => throw "expecting slice"
  return .tuple l

-- Handle subscript expressions, t[i]
def access (e : Term) (indexes : List Term) : Err Term := do
  match e with
  | .string _ => throw "string subscript not implemented"
  | .tuple l
  | .list l => listAccess l indexes
  | .pointer addr => pointerAccess addr indexes
  | .mgrid => mgrid indexes
  | .expr _e _ => do
      -- TODO: support Access
      let tensor : Core.TensorName <- fromNKI? e
      let indices <- toIndex tensor.shape.toList indexes
      let access <- Core.Access.mkBasic tensor indices
      let shape <- access.shape
      return .expr (.value (.access access)) (.tensor tensor.dtype shape)
  | _ => throw "subscript not supported"

/-
# Attributes

This code handles projection, a.k.a. attribute access.

TODO: For now we ignore unknown names in NKI modules.
Once the Python APIs are updated we can stop doing this.
-/

def Term.attr : Term -> String -> Trace Term
  | .module n, id => do
     let name := n.str id
     try lookup name
     catch _ =>
       if isNKI name
       then return .expr (.value $ .var name.toString) (.obj name)
       else throw s!"{id} is not in module {n}"
  | .pointer addr, "start" => return tuple [addr.parOffset, addr.freeOffset]
  | .pointer addr, "size" => return tuple [addr.parSize, addr.freeSize]
  | .pointer addr, "view" => return memViewBuiltin addr
  | .expr _ (.tensor d _), "dtype" => return (dtype d)
  | .expr _ (.tensor _ s), "shape" => return (tuple $ s.toList.map some)
  | .expr _ (.obj n), id => lookup (n.str id)
  | _, id => throw s!"unsupported attribute {id}"
where
  dtype dty :=
    let name := "neuronxcc.nki.language." ++ dstr dty
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
  isNKI : Name -> Bool
  | .str `neuronxcc.nki _ => true
  | .str n _ => isNKI n
  | _ => false



nki memView (self : Address) (dtype : Dtype) (shape : Shape) (name : String := "tensor") := do
  let name := (<- genName (.mkStr1 name)).toString
  if parWF: shape.parDim <= self.parSize then
    if freeWF: shape.freeElements * dtype.size <= self.freeSize then
      let tensor := ⟨ name, dtype, shape, self, shape.freeElements, parWF, freeWF ⟩
      let ty := TermType.tensor dtype shape
      return .expr (.value (.access (.simple tensor))) ty
    else throw "shape is too large for memory region"
  else throw "partition size is too large for memory region"

-- TODO reorganize these
nki par_dim (t : Term) := do
  warn "par_dim is deprecated"
  return t

nki ndarray
  (shape : Shape)
  (dtype : Dtype)
  (buffer : Option Memory := none)
  (name : Option String := none) := do
    let memory := buffer.getD .sbuf
    let (parSize, freeSize) := Address.defaultSize shape dtype
    let address := { memory, parSize, freeSize : Address }
    let name := name.getD "tensor"
    let tensor <- TensorName.make name dtype shape address
    return .expr (.value $ .access (.simple tensor)) (.tensor dtype shape)

nki python_len (t : Term) := do
  match t with
  | .tuple l | .list l => return .expr (.value (.int l.length)) .int
  | _ => throw "invalid argument"

-- TODO: should take arbitrary number of arguments and work on more types
nki python_min (a : Term) (b : Term) := do
  match a, b with
  | .expr (.value (.int a)) _, .expr (.value (.int b)) _ =>
     return .expr (.value (.int (min a b))) .int
  | _, _ => throw "invalid arguments"

/-
# Static environment of builtins

Builtin functions only operate on terms. Note this environment is separate from
the evaluation environment. All of the entries in this environment will have
corresponding entries in the main evaluation environment which redirect to this
environment. For example, the main environment will contain:

  nki.isa.dropout => .builtin `nki.isa.dropout

and the builtin environment will then contain:

  nki.isa.dropout => <lean function>

This indirection is necessary because the builtin implementations take terms
and live in the Trace monad, which contains an environment of terms.
-/

private def nl : String -> Name := .str `neuronxcc.nki.language

def builtinEnv : List (Name × BuiltinFn) :=
  (memViewName, memView) ::
  (nl "par_dim", par_dim) ::
  (nl "ndarray", ndarray) ::
  ( `len, python_len) ::
  ( `min, python_min) ::
  Isa.builtins

def builtinFn (name : Name) : Trace BuiltinFn :=
  match builtinEnv.lookup name with
  | some f => return f
  | none => throw s!"unimplemented API {name}"
