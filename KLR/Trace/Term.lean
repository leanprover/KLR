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
import KLR.Trace.Lang
import KLR.Trace.Python
import KLR.Trace.Types

/-
# Basic tracing facilities

Basic tracing definitions only deal with Terms (not Python sources)
-/

namespace KLR.Trace
open Core

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

private def uintOp (op : BinOp) (l r : UInt64) : Trace Term :=
  let ret (x : UInt64) : Trace Term := return (Int.ofNat x.toNat)
  match op with
  | .lshift => ret (l <<< r)
  | .rshift => ret (l >>> r)
  | .or => ret (l ||| r)
  | .xor => ret (l ^^^ r)
  | .and => ret (l &&& r)
  | _ => throw "unsupported operator on integers"

private def intOp (op : BinOp) (l r : Int) : Trace Term :=
  match op with
  | .add => return l + r
  | .sub => return l - r
  | .mul => return l * r
  | .div => if r = 0 then throw "division by zero" else
            return Float.ofInt l / Float.ofInt r
  | .mod => return l % r
  | .pow => return l.pow r.toNat
  | .floor => if r = 0 then throw "division by zero" else
              return l / r
  | _ => uintOp op (UInt64.ofInt l) (UInt64.ofInt r)

private def floatOp (op : BinOp) (l r : Float) : Trace Term :=
  match op with
  | .add => return l + r
  | .sub => return l - r
  | .mul => return l * r
  | .div => return l / r
  | .pow => return l.pow r
  | .floor => return (l / r).floor
  | _ => throw "unsupported operator on floating point numbers"

-- Note: both Lean and Python use big integers
-- TODO: imcomplete
private def valueOp : BinOp -> Value -> Value -> Trace Term
  -- tensors
  | _, .access _, _
  | _, _, .access _ =>
    throw "binary operators on tensors not supported. Use nki.isa directly."
  -- integers
  | op, .int l, .int r => intOp op l r
  | op, .int l, .bool r => intOp op l r.toInt
  | op, .bool l, .int r => intOp op l.toInt r
  -- floats
  | op, .float l, .float r => floatOp op l r
  | op, .float l, .int r => floatOp op l (Float.ofInt r)
  | op, .int l, .float r => floatOp op (Float.ofInt l) r
  | op,_,_ => throw s!"unimplemented operator {op}"

-- Binary operators on tensors (see Tensor.lean)
private def exprOp : BinOp -> Expr -> Expr -> Trace Term
  | op, .value l, .value r => valueOp op l r
  | _ , _       , _        => throw "non-constant expression"

-- Binary operators on terms
-- TODO mulseq on strings
def termOp : BinOp -> Term -> Term -> Trace Term
  -- lists and tuples
  | .add, .string l,        .string r => return .string (l ++ r)
  | .add, .list   l,        .list   r => return .list (l ++ r)
  | .add, .tuple  l,        .tuple  r => return .tuple (l ++ r)
  | .mul, .list   l,        .expr (.value  v)
  | .mul, .expr (.value v), .list l   => return .list (<- mulseq l v)
  | .mul, .tuple  l,        .expr (.value  v)
  | .mul, .expr (.value v), .tuple l  => return .tuple (<- mulseq l v)
  -- mgrid
  | .add, .expr (.value (.int i)), .mgItem a b s
  | .add, .mgItem a b s, .expr (.value (.int i)) => return .mgItem (a+i) (b+i) (s+1)
  | .add, .mgItem a b c, .mgItem x y z => return .mgItem (a+x) (b+y) (c+z)
  | .mul, .expr (.value (.int i)), .mgItem a b s
  | .mul, .mgItem a b s, .expr (.value (.int i)) => return .mgItem (a*i) (b*i) (s*1)
  -- expressions
  | op, .expr l, .expr r => exprOp op l r
  | _, _, _ => throw "unsupported operator"

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
  | .expr e₁, .expr e₂ => exprEq e₁ e₂
  | _, _ => return false
where
  teq : List Term -> List Term -> Trace Bool
    | [], [] => return true
    | x :: xs, y :: ys => return (<- termEq x y) && (<- teq xs ys)
    | _, _ => return false

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
  | .expr (.value l), .expr (.value r) => valueLt l r
  | _, _ => throw "unsupported comparison"
where
  listLt : List Term -> List Term -> Trace Bool
  | [], [] => return false
  | [], _ => return true
  | _, [] => return false
  | x :: xs, y :: ys => do
      if <- termLt x y then return true
      else return (<- termEq x y) && (<- listLt xs ys)

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
    | .mgItem s e t =>
        return .slice (<- Core.Slice.make s.toNat e.toNat t) :: (<- toIndex ds ts)
    | t => do
        let i : Int <- fromNKI? t
        if i < 0 || i >= d then
          throw "index out of range of tensor dimension"
        return .coord i.toNat :: (<- toIndex ds ts)


-- Note, a list index can be negative, which means index from end of list.
-- Python also allows l[True] and l[False]
-- TODO: add case for slice
def listAccess (l : List Term) : List Term -> Err Term
  | [.expr (.value (.bool false))] => do
      if h:l.length > 0 then return l.get (Fin.mk 0 h)
      else throw "index out of bounds"
  | [.expr (.value (.bool true))] => do
      if h:l.length > 1 then return l.get (Fin.mk 1 h)
      else throw "index out of bounds"
  | [.expr (.value (.int i))] => do
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
    .pointer { name := addr.name
               memory := addr.memory
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
      let c := c.getD 1
      l := l ++ [.mgItem a b c]
    | _ => throw "expecting slice"
  match l with
  | [] => throw "mgrid must have at least 1 dimension"
  | [t] => return t
  | _ => return .tuple l

-- Handle subscript expressions, t[i]
def access (e : Term) (indexes : List Term) : Err Term := do
  match e with
  | .string _ => throw "string subscript not implemented"
  | .tuple l
  | .list l => listAccess l indexes
  | .pointer addr => pointerAccess addr indexes
  | .mgrid => mgrid indexes
  | .expr _ => do
      -- TODO: support Access
      let tensor : Core.TensorName <- fromNKI? e
      let indices <- toIndex tensor.shape.toList indexes
      let access <- Core.Access.mkBasic tensor indices
      return .expr (.value (.access access))
  | _ => throw "subscript not supported"

/-
# Attributes

This code handles projection, a.k.a. attribute access.

TODO: For now we ignore unknown names in NKI modules.
Once the Python APIs are updated we can stop doing this.
-/

private def offset (a : Access) : Trace Term := do
  let bap <- a.lowerAccessPattern
  return bap.offset

private def pattern (a : Access) : Trace Term := do
  let bap <- a.lowerAccessPattern
  let pairs := bap.pattern.map fun p =>
    Term.tuple [Term.int p.step, Term.nat p.num]
  return .tuple pairs

def Term.attr : Term -> String -> Trace Term
  | .module n, id => lookup (.str n id)
  | .pointer addr, "name" => return .string addr.name
  | .pointer addr, "start" => return tuple [addr.parOffset, addr.freeOffset]
  | .pointer addr, "size" => return tuple [addr.parSize, addr.freeSize]
  | .pointer addr, "ptr" => return memPtrBuiltin addr
  | .pointer addr, "view" => return memViewBuiltin addr
  | .expr (.value (.access a)), "dtype" => return (dtype a.tensor.dtype)
  | .expr (.value (.access a)), "shape" => return (tuple $ a.shapePure.toList.map some)
  | .expr (.value (.access a)), "address" => return .pointer a.tensor.address
  | .expr (.value (.access a)), "offset" => offset a
  | .expr (.value (.access a)), "pattern" => pattern a
  | t@(.expr (.value (.access _))), "reshape" => return reshapeBuiltin t
  | .expr (.value (.var n)), id => lookup (.str n.toName id)
  | _, id => throw s!"unsupported attribute {id}"
where
  dtype dty :=
    let name := "neuronxcc.nki.language." ++ dstr dty
    .expr (.value $ .var name)
  tuple (l : List (Option Nat)) : Term :=
    Term.tuple $ l.map fun
      | Option.none => Term.none
      | some x => .expr (.value (.int x))
  dstr dty :=
    let s := reprStr dty
    match s.toName with
    | .str _ s => s
    | _ => panic! "internal error (dtype name)"

nki builtin.memPtr
    (self : Address)
    (size : (Nat × Nat))
    (offset : Option (Nat × Nat) := none)
    (name : Option String := none) := do
  let name <- tensorName name
  let memory := self.memory
  let parSize := size.1
  let freeSize := size.2
  let (parOffset, freeOffset) := match offset with
    | none => (none, none)
    | some (x, y) => (some x, some y)
  return .pointer {
    name, memory,
    parSize, freeSize,
    parOffset, freeOffset
  }

nki builtin.memView
    (self : Address)
    (dtype : Dtype)
    (shape : Shape)
    (name : Option String := none) := do
  let name <- tensorName name
  if parWF: shape.parDim <= self.parSize then
    if freeWF: shape.freeElements * dtype.size <= self.freeSize then
      let tensor := ⟨ name, dtype, shape, self, shape.freeElements, parWF, freeWF ⟩
      return .expr (.value (.access (.simple tensor)))
    else throw "shape is too large for memory region"
  else throw "partition size is too large for memory region"

nki builtin.reshape
    (self : Access)
    (shape : List Nat)
    (dtype : Option Dtype := none)
    (name : Option String := none) := do
  let tensor <- match self with
    | .simple t => pure t
    | _ => throw "cannot reshape a complex access pattern"
  let dtype := dtype.getD tensor.dtype
  let name <- tensorName name
  let shape <- Shape.fromList shape
  let t <- TensorName.make name dtype shape tensor.address
  return .expr (.value (.access (.simple t)))

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

The builtin environment is tracked as a Lean environment extension (see Builtin.lean).
We extract the builtins into a list here. Note, this means all modules with builtins
should be imported into this module.
-/

open Lean in
run_meta
  let builtins : Builtins := extension.getState (<- getEnv)
  let mut set : Std.HashSet Name := Std.HashSet.emptyWithCapacity builtins.builtins.size
  let mut pairs := #[]
  for builtin in builtins.builtins do
    if set.contains builtin.nkiName then
      throwError s!"{builtin.nkiName} ({builtin.leanName}) redefined"
    set := set.insert builtin.nkiName
    let str := Syntax.mkStrLit builtin.nkiName.toString
    let trm := mkIdent builtin.leanName
    let pair <- `( ( $(str).toName, $trm:term ))
    pairs := pairs.push pair
  let name := mkIdent (Name.str (<- getCurrNamespace) "builtinFns")
  let cmd <- `( def $name : List (Name × BuiltinFn) := [ $pairs,* ] )
  liftCommandElabM (Elab.Command.elabCommand cmd)

def builtinFn (name : Name) : Trace BuiltinFn :=
  match builtinFns.lookup name with
  | some f => return f
  | none => throw s!"unimplemented API {name}"

/-
We have a convention on naming, but this is temporary while the NKI APIs
are being rewritten. For now, we register names in the builtin namespace
to public names, e.g. builtin.isa.X => nki.isa.X.
-/
def builtinEnv : List (Name × Term) := Id.run do
  builtinFns.flatMap fun (name, _) =>
    let fn := .builtin name none
    let names : List Name := match name with
      | .str `builtin.python n => [.str .anonymous n]
      | .str `builtin.isa n => [nisa n, name]
      | .str `builtin.lang n => [nl n, name]
      | _ => [name]
    names.map fun n => (n, fn)
