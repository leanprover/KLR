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
import KLR.Trace.Tensor
import KLR.Core.Indexing

/-
# Basic tracing facilities

Basic tracing definitions only deal with Terms (not Python sources)
-/

namespace KLR.Trace
open Core (Access Address Dtype Index Shape Slice TensorName)

-- Binary Operators

-- Multiply a sequence (tuple, list, string) by a scalar
-- It is tempting to use Const.toInt here, but that would be
-- more permissive than Python. The only allowed cases are:
--   [1,2] * 2     => [1,2,1,2]
--   [1,2] * 0     => []
--   [1,2] * -10   => []
--   [1,2] * True  => [1,2]
--   [1,2] * False => []

private def mulseq (l : List a) : Term -> Err (List a)
  | .bool false => return []
  | .bool true  => return l
  | .int i      => return List.flatten $ List.replicate i.toNat l
  | t           => throw s!"can't multiply sequence by '{Term.kindStr t}'"

-- Binary operators on constants

private def uintOp (op : BinOp) (l r : UInt64) : Trace Term :=
  let ret (x : UInt64) : Trace Term := return .int (Int.ofNat x.toNat)
  match op with
  | .lshift => ret (l <<< r)
  | .rshift => ret (l >>> r)
  | .or => ret (l ||| r)
  | .xor => ret (l ^^^ r)
  | .and => ret (l &&& r)
  | op => throw s!"integers do not support operator '{repr op}'"

private def intOp (op : BinOp) (l r : Int) : Trace Term :=
  match op with
  | .add => return .int (l + r)
  | .sub => return .int (l - r)
  | .mul => return .int (l * r)
  | .div => if r = 0 then throw "division by zero" else
            return .float (Float.ofInt l / Float.ofInt r)
  | .mod => return .int (l % r)
  | .pow => return .int (l.pow r.toNat)
  | .floor => if r = 0 then throw "division by zero" else
              return .int (l / r)
  | _ => uintOp op (UInt64.ofInt l) (UInt64.ofInt r)

private def floatOp (op : BinOp) (l r : Float) : Trace Term :=
  let ret (x : Float) : Trace Term := return .float x
  match op with
  | .add => ret (l + r)
  | .sub => ret (l - r)
  | .mul => ret (l * r)
  | .div => ret (l / r)
  | .pow => ret (l.pow r)
  | .floor => ret (l / r).floor
  | _ => throw s!"floating point numbers do not support operator '{repr op}'"

private def tensorBinOp(op : BinOp) (l r : TensorLib.Tensor) : Trace Term := do
  let dt := l.dtype
  match op with
  | .add => return .tensor $ <- iterBinOp l r (fun x y => dt.add! x y)
  | .sub => return .tensor $ <- iterBinOp l r (fun x y => dt.sub! x y)
  -- TODO : implement multiplication and division
  | _ => throw s!"tensors do not support scalar operator '{repr op}'"

-- Note: both Lean and Python use big integers
-- TODO: imcomplete
private def valueOp : BinOp -> Term -> Term -> Trace Term
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
  -- tensors
  | op, .tensor l, .float r => tensorOpScalarFloat op l r
  | op, .tensor l, .int r => tensorOpScalarInt op l r
  | op, .tensor l, .tensor r => tensorBinOp op l r
  | op,_,_ => throw s!"unimplemented operator '{op}'"

-- Binary operators on terms
-- TODO mulseq on strings
private def termOp : BinOp -> Term -> Term -> Trace Term
  -- lists and tuples
  | .add, .string l, .string r => return .string (l ++ r)
  | .add, .list   l, .list   r => return .list (l ++ r)
  | .add, .tuple  l, .tuple  r => return .tuple (l ++ r)
  | .mul, .list   l, v
  | .mul, v        , .list l   => return .list (<- mulseq l.toList v).toArray
  | .mul, .tuple  l, v
  | .mul, v        , .tuple l  => return .tuple (<- mulseq l v)
  -- expressions
  | op, l, r => valueOp op l r

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

private def valueLt : Term -> Term -> Trace Bool
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
  | l, r => throw s!"unsupported comparison between '{Term.kindStr l}' and '{Term.kindStr r}'"

-- Note, this is partial because the user could have created
-- a graph in the heap
private partial def termLt : Term -> Term -> Trace Bool
  -- references
  | .ref l _, r => do termLt (<- lookup l) r
  | l, .ref r _ => do termLt l (<- lookup r)
  -- list-like types
  | .string l, .string r => return l < r
  | .tuple l, .tuple r => listLt l r
  | .list  l, .list  r => listLt l.toList r.toList
  -- values
  | l, r => valueLt l r
where
  listLt : List Term -> List Term -> Trace Bool
  | [], [] => return false
  | [], _ => return true
  | _, [] => return false
  | x :: xs, y :: ys => do
      if <- termLt x y then return true
      else return (x == y) && (<- listLt xs ys)

private def binop' (op : BinOp) (l r : Term) : Trace Term := do

  let resolveTerm := fun t => match t with
    | .var name => do
        match <- lookup? name with
        | some (.source {name, ..}) => pure (.var name)
        | some t => pure t
        | none => pure .none
    | .source {name, ..} => pure (.var name)
    | _ => pure t
  let l <- resolveTerm l
  let r <- resolveTerm r

  match op with
  -- logical
  | .land => return .bool ((<- l.isTrue) && (<- r.isTrue))
  | .lor  => return .bool ((<- l.isTrue) || (<- r.isTrue))
  -- comparison
  | .eq => return .bool (l == r)
  | .ne => return .bool (l != r)
  | .lt => return .bool (<- termLt l r)
  | .le => return .bool (l == r || (<- termLt l r))
  | .gt => return .bool ((not (l == r)) && (not (<- termLt l r)))
  | .ge => return .bool (not (<- termLt l r))
  -- arithmetic / bitwise
  | _ => termOp op l r

def binop (op : BinOp) (l r : Term) : Trace Term := do
  let l <- match l with
    | .ref name _ => lookup name
    | _ => pure l
  let r <- match r with
    | .ref name _ => lookup name
    | _ => pure r
  binop' op l r

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
def toIndex' (shape : List Nat) (ts : List Term) : Err (List Index) := do
  let slice (d : Nat) := (Slice.make 0 d 1).map .slice
  match shape, ts with
  | [], []
  | [], [.ellipsis] => return []
  | [], _  => throw "too many indexes for shape"
  | ds, [] => ds.mapM slice
  | d :: ds, t :: ts =>
    match t with
    | .none => return (<- slice d) :: (<- toIndex' ds ts)
    | .ellipsis =>
        if ds.length + 1 == ts.length
        then toIndex' (d::ds) ts
        else return (<- slice d) :: (<- toIndex' ds (t::ts))
    | .slice x y z => do
        let d := Int.ofNat d
        let x := x.getD 0
        let y := y.getD d
        let z := z.getD 1
        let x := if x < 0 then d + x else x
        let y := if y < 0 then d + y else y
        if x < 0 || x >= d || y < 0 || y > d || z <= 0 then
          throw "index out of range of tensor dimension"
        return .slice (<- Slice.make x.toNat y.toNat z) :: (<- toIndex' ds ts)
    | .tuple _ | .list  _ => throw "nested tuple/list indexes not supported"
    | t => do
        let i : Int <- fromNKI? t
        if i < 0 || i >= d then
          throw "index out of range of tensor dimension"
        return .coord i.toNat :: (<- toIndex' ds ts)

def toIndex (shape : List Nat) (ts : List Term) : Err (List Index) := do
  let ts := match ts with
    | [.tuple l] => l
    | [.list a] => a.toList
    | _ => ts
  toIndex' shape ts

-- Container type information for preserving original types during access
inductive ContainerType where
  | tuple : ContainerType
  | list : ContainerType
  deriving Repr, BEq

-- Note, a list index can be negative, which means index from end of list.
-- Python also allows l[True] and l[False]
-- TODO: add case for slice
def listAccess (l : List Term) (containerType : Option ContainerType := none) : List Term -> Err Term
  | [.bool false] => do
      if h:l.length > 0 then return l.get (Fin.mk 0 h)
      else throw "index out of bounds"
  | [.bool true] => do
      if h:l.length > 1 then return l.get (Fin.mk 1 h)
      else throw "index out of bounds."
  | [.int i] => do
      let i := if i < 0 then l.length + i else i
      if i < 0 then throw s!"negative index ({i}) out of bounds"
      let n := i.toNat
      if h:l.length > n then return l.get (Fin.mk n h)
      else throw s!"index ({n}) out of bounds"
  | [.slice start u step] => do
      let start := start.getD 0
      let e := u.getD l.length
      let step := step.getD 1
      if step <= 0 then throw "slice step cannot be zero or negative"
      let start := if start < 0 then l.length + start else start
      let e := if e < 0 then l.length + e else e
      if start < 0 || start > l.length || e < 0 || e > l.length then
        throw "slice index out of bounds"
      let sliced := List.range ((e - start + step - 1) / step).toNat |>.map fun i =>
        l[start.toNat + i * step.toNat]!
      match containerType with
      | some .tuple => return .tuple sliced
      | some .list | none => return .list sliced.toArray
  | e => throw s!"index must be an integer or slice, got {repr e}"

def dictAccess (arr : AA) : List Term -> Err Term
  | [t] => do
      let s : String <- fromNKI? t
      match arr.lookup? s with
      | none => throw s!"key {s} not found in dictionary"
      | some t => return t
  | _ => throw "expecting single string argument in dictionary access"

/-
Access to pointer types (a.k.a. Address)
NKI users can define memory regions by using slices on other memory regions.
Initially, the regions `sbuf` and `psum` are defined. For example:

  ptr = sbuf[0:32, 0:512]  # memory region in SBUF
  ptr2 = ptr[:, :256]      # left half of region
  ptr3 = ptr[:, 256:]      # right half of region

https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/nki_arch_guides.html
-/

def pointerAccess (addr : Address) (i : List Term) : Err Term := do
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

  let chkPslice (s : Slice) : Err (Option Nat × Nat) := do
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

  let chkFslice (s : Slice) : Err (Option Nat × Nat) := do
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

-- Handle subscript expressions, t[i]
-- Note: partial due to possible heap graphs
partial def access (e : Term) (indexes : List Term) : Trace Term := do
  match e with
  | .ref name _ => access (<- lookup name) indexes
  | .string _ => throw "string subscript not implemented"
  | .tuple l => listAccess l (some .tuple) indexes
  | .list l => listAccess l.toList (some .list) indexes
  | .dict arr => dictAccess arr indexes
  | .pointer addr => pointerAccess addr indexes
  | .access (.simple tensor) => do
      -- TODO: support Access
      let indices <- toIndex tensor.shape.toList indexes
      let access <- Access.mkBasic tensor indices
      return .access access
  | .access (.basic tensor) => do
    let indices <- toIndex (<-tensor.shape).toList indexes
    let ac <- Access.combine (.basic tensor) indices
    return .access (.pattern ac)
  | .access (.pattern pattern) => do
    let indices <- toIndex pattern.tensor.shape.toList indexes
    let ac <- Access.combine (.pattern pattern) indices
    return .access (.pattern ac)
  | t => throw s!"subscript not supported, for '{Term.kindStr t}'"

/-
# Attributes

This code handles projection, a.k.a. attribute access.

TODO: For now we ignore unknown names in NKI modules.
Once the Python APIs are updated we can stop doing this.
-/

private def offset (a : Access) : Trace Term := do
  let unsafeCast <- flags.unsafe_cast_fp8fncast
  let state : Core.LowerAPState := { unsafeCast }
  let bap <- (a.lowerAccessPattern).run' state
  return .int bap.offset

private def pattern (a : Access) : Trace Term := do
  let unsafeCast <- flags.unsafe_cast_fp8fncast
  let state : Core.LowerAPState := { unsafeCast }
  let bap <- (a.lowerAccessPattern).run' state
  let pairs := bap.pattern.map fun p =>
    Term.tuple [.int p.step, .int p.num]
  return .tuple pairs

def Term.attr (t : Term) (id : String) : Trace Term :=
  match t with
  | .module n
  | .builtin n _
  | .source { name := n, ..}
  | .var n => lookup (.str n id)
  | .ref _ .list =>
      match id with
      | "append"
      | "clear"
      | "copy"
      | "count"
      | "extend"
      | "index"
      | "pop"
      | "remove"
      | "reverse"
      | "sort" => return .builtin (.str `builtin.list id) (some t)
      |  _ => throw s!"{id} is not an attribute of list"
  | .ref _ .dict =>
      match id with
      | "clear"
      | "copy"
      | "get"
      | "items"
      | "keys"
      | "pop"
      | "setdefault"
      | "values" => return .builtin (.str `builtin.dict id) (some t)
      |  _ => throw s!"{id} is not an attribute of dict"
  | .ref name (.object c) => do
      match <- lookup? name with
      | some (.object c' fs) =>
        if c != c' then
          throw s!"internal error: reference {name}:{c} points to obj:{c'}"
        match AA.lookup? fs id with
        | .some t => return t
        | .none =>
          match <- lookup? (.str c id) with
          | some (.source _) =>  return .method c id name
          | _ => throw s!"{id} is not an attribute of {c}"
      | _ => throw s!"internal error: ref({name}:{c}) not found"
  | .pointer addr =>
      match id with
      | "name" => return .string addr.name
      | "start" => return tuple [addr.parOffset, addr.freeOffset]
      | "size" => return tuple [addr.parSize, addr.freeSize]
      | "ptr" => return .builtin `builtin.pointer.ptr t
      | "view" => return .builtin `builtin.pointer.view t
      |  _ => throw s!"unsupported attribute {id} (type is pointer)"
  | .access a =>
      match id with
      | "dtype" =>
        match a with
        | .birPattern b =>
          match b.dtypeOverride with
          | some dt => return <- dtype dt
          | _ => return <- dtype b.tensor.dtype
        | _ => return <- dtype a.tensor.dtype
      | "shape" => do
        match a.toAP with
        | .ok ap => return (tuple $ ap.shape.toList.map some)
        -- fallback for being unable to convert ap to access pattern. Should not fire
        | .error _ => return (tuple $ a.shapePure.toList.map some)
      | "address" => return .pointer a.tensor.address
      | "offset" => offset a
      | "pattern" => pattern a
      | "reshape" => return .builtin `builtin.access.reshape t
      | "ap" => return .builtin `builtin.access.ap t
      | "buffer" => return .var (`nki.language ++ a.tensor.address.memory.toName)
      | "view" => return .builtin `builtin.pointer.view (some $ .pointer a.tensor.address)
      | "name" => return .string a.tensor.name
      | "address_name" => return .string a.tensor.address.name
      | _ => throw s!"unsupported attribute {id} (type is tensor access)"
  | .slice a b c =>
      let opt : Option Int -> Term
        | .none => .none
        | .some i => .int i
      match id with
      | "start" => return opt a
      | "stop" => return opt b
      | "step" => return opt c
      | _ => throw s!"{id} is not an attribute {id} of slice"
  | _ => throw s!"unsupported attribute {id}"
where
  dtype dty := do
    match dname dty with
    | some name => do
        match <- lookup? name with
        | some t => return t
        | _ => return .string (dstr dty)
    | _ => return .string (dstr dty)
  tuple (l : List (Option Nat)) : Term :=
    Term.tuple $ l.map fun
      | Option.none => Term.none
      | some x => .int x
  dname dty :=
    let s := reprStr dty
    match s.toName with
    | .str _ s => some $ `nki.language ++ s.toName
    | _ => Option.none
  dstr dty :=
    let s := reprStr dty
    match s.toName with
    | .str _ s => s
    | _ => "unknown"

nki builtin.pointer.ptr
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

nki builtin.pointer.view
    (self : Address)
    (dtype : Dtype)
    (shape : Shape)
    (name : Option String := none)
    (address_rotation : Option Bool := none) := do
  let name <- tensorName name
  let self := {self with name := name}
  let address_rotation <- match address_rotation with
  | some v => pure v
  | none => flags.address_rotation
  if parWF: shape.parDim <= self.parSize then
    if freeWF: shape.freeElements * dtype.size <= self.freeSize then
      let tensor := ⟨ name, dtype, shape, self, shape.freeElements, parWF, freeWF, address_rotation ⟩
      if self.memory == .shared_hbm || self.memory == .hbm then
        Trace.addSharedBuffer tensor
      return .access (.simple tensor)
    else throw "shape is too large for memory region"
  else throw "partition size is too large for memory region"

nki builtin.access.reshape
    (self : Access)
    (shape : List Nat)
    (dtype : Option Dtype := none)
    (name : Option String := none)
    (address_rotation : Option Bool := none) := do
  let tensor <- match self with
    | .simple t => pure t
    | _ => throw "cannot reshape a complex access pattern"
  let dtype := dtype.getD tensor.dtype
  let name <- tensorName name
  let shape' <- Shape.fromList shape

  let address_rotation <- match address_rotation with
  | some v => pure v
  | none => flags.address_rotation

  let addr <- if tensor.address.memory.isHBM then
      let shape_sz := shape.foldl (. * .) tensor.dtype.size
      let addr_sz := tensor.address.parSize * tensor.address.freeSize
      if addr_sz < shape_sz then
        throw s!"shape has size {shape_sz} (bytes), \
                 which is too large for buffer of size {addr_sz} (bytes)"
      let addr := Address.withDefaultSize tensor.address shape' dtype
      pure addr
    else
      pure tensor.address
  let t <- TensorName.make name dtype shape' addr address_rotation
  return .access (.simple t)

nki builtin.access.ap
    (self : Access)
    (pattern : List (Int × Nat))
    (offset : Nat := 0)
    (scalar_offset : Option (Sum Access Term) := none)
    (vector_offset : Option Access := none)
    (indirect_dim : Int := 0)
    (dtype : Option Dtype := none) := do
  match self with
  | .simple t =>
      let pattern := pattern.map fun (s,c) => Core.APPair.mk s c 0
      let scalarOffset <- scalar_offset.mapM fun
        | .inl a => pure (.acc a)
        | .inr r => match r with
          | .scalar s => pure (.reg s.toString)
          | _ => throw s!"scalar_offset requires scalar argument, got {r.kindStr}"
      let ap : Core.BirAccessPattern := {
        tensor := t
        offset
        pattern
        scalarOffset
        vectorOffset := vector_offset
        indirectDim := indirect_dim
        dtypeOverride := dtype
      }
      return .access (.birPattern ap)
  -- TODO: need to figoure out how to combine cannonical form AP with user specified AP
  -- The difficulty lies in understanding which portions of AP does offset belong to
  -- | .basic _ =>
  --   let pat := pattern.map fun (s,c) => Core.APPair.mk s c 0
  --   let ac <- Access.combineAP self { pairs := pat, fixedAxis := [] }
  --   return .access (.pattern ac)
  | _ => throw s!"cannot specify an access pattern on an already indexed tensor"

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
      | .str `builtin.python n => [.str `builtins n, .str .anonymous n]
      | .str `builtin.typing n => [nt n, name]
      | .str `builtin.lang n => [nl n, name]
      | .str `builtin.meta.tensor n => [ntensor n, name]
      | _ => [name]
    names.map fun n => (n, fn)
