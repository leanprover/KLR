/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Core
import KLR.Python
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Basic
import TensorLib

namespace KLR.Trace
open KLR.Python
open Core (tensors Slice)

def const : Const -> Term
  | .none     => .none
  | .bool b   => .expr (.value $ .bool b)   .bool
  | .int i    => .expr (.value $ .int i)    .int
  | .float f  => .expr (.value $ .float f)  .float
  | .string s => .string s
  | .ellipsis => .ellipsis

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

-- Convert a Term to an Index (if possible)
def termToIndex (shape : List Nat) : Term -> Err (List Core.Index)
  | .tuple l | .list l => toIndex shape l
  | t => toIndex shape [t]
where
  slice (d : Nat) := (Slice.make 0 d 1).map .slice
  toIndex : List Nat -> List Term -> Err (List Core.Index)
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
        return .slice (<- Slice.make x.toNat y.toNat z) :: (<- toIndex ds ts)
    | .tuple _ | .list  _ => throw "nested tuple/list indexes not supported"
    | t => do
        let i : Int <- fromNKI? t
        if i < 0 || i >= d then
          throw "index out of range of tensor dimension"
        return .coord i.toNat :: (<- toIndex ds ts)

-- Note, a list index can be negative, which means index from end of list.
-- Python also allows l[True] and l[False]
-- TODO: add case for slice
def listAccess (name : String) (l : List Term) : Term -> Err Term
  | .expr (.value (.bool false)) _ => do
      if h:l.length > 0 then return l.get (Fin.mk 0 h)
      else throw "index out of bounds"
  | .expr (.value (.bool true)) _ => do
      if h:l.length > 1 then return l.get (Fin.mk 1 h)
      else throw "index out of bounds"
  | .expr (.value (.int i)) _ => do
      let i := if i < 0 then l.length + i else i
      if i < 0 then throw "index out of bounds"
      let n := i.toNat
      if h:l.length > n then return l.get (Fin.mk n h)
      else throw "index out of bounds"
  |_ => throw s!"{name} indicies must be integers of slices"


/-
  Given an int tensor t of N dimensions, find 'steps' which is a list of N
  s.t. for every i1,i2,..,
    t[i1,i2,...] = t[0,0,...] + (i1,i2,..) ⬝ steps
  where + is an elementwise addition and ⬝ is a dot product.

  For example, if t is [[10, 15], [30, 35]], valAtZero is 10, and
  steps = [5, 20].
  t[1,1] = 35 = 10 + (1,1) ⬝ (5,20)

  Returns: ⟨ t[0,0,...], steps ⟩
  For the above example, the return value is ⟨ 10, [5, 20] ⟩
-/
def decomposeLinearIntTensor (t:TensorLib.Tensor)
    : Err (Int × List (Core.APPair)) := do
  match t.dtype with
  | TensorLib.Dtype.uint64 | TensorLib.Dtype.int64 =>
    let dimsize := t.shape.val.length
    let zerocoord := List.replicate dimsize 0
    -- Get the value at t[0,..,0]
    let valAtZero <- t.intAtDimIndex zerocoord
    -- And get 't[0,..,1,..,0] - t[0,..,0,..,0]' to get the size of step
    let steps <- List.mapM (fun i => do
        if List.getD t.shape.val i 0 ≤ 1
        then return 0 -- t is too small in this axis to calculate the step
        else
          let nextcoord := List.set zerocoord i 1
          let valAtOne ← t.intAtDimIndex nextcoord
          return valAtOne - valAtZero
      ) (List.range dimsize)
    -- Check whether t[idx] = valAtZero + idx * steps for all indices
    let _ <- check [] dimsize steps valAtZero
    return ⟨
      valAtZero,
      List.map (fun (sz, step) => { step := step, num := sz : Core.APPair })
        (List.zip t.shape.val steps)
    ⟩
  | _ => throw s!"supports uint64 or int64 only, but got {repr t.dtype}"
where
  check (idx:List Nat) (cnt:Nat) (steps:List Int) (valAtZero:Int)
      : Err Bool := do
    let l := idx.length
    if cnt > 0 then
      let r := List.range (List.getD t.shape.val l 0)
      List.allM (fun k => check (idx ++ [k]) (cnt - 1) steps valAtZero) r
    else
      let mult: List Int := List.map
        (fun (a,b) => (Int.ofNat a) * b) (List.zip idx steps)
      let dot: Int := mult.foldl (fun a b => a + b) 0
      let lhs: Int <- t.intAtDimIndex idx
      return decide (lhs = valAtZero + dot)


#guard match (decomposeLinearIntTensor
    (TensorLib.Tensor.zeros TensorLib.Dtype.int64
      { val := [10, 10] : TensorLib.Shape})) with
      | .error _ => false
      | .ok (valAtZero, steps) =>
        valAtZero = 0 ∧
        steps == [
          { step := 0, num := 10 : Core.APPair },
          { step := 0, num := 10 : Core.APPair }]

#guard match (do
      let tensor <- TensorLib.Tensor.ofIntList TensorLib.Dtype.int64
        [10, 20, 30, 40, 50, 60]
      let tensor2d <- tensor.reshape (TensorLib.Shape.mk [2, 3])
      decomposeLinearIntTensor tensor2d) with
      | .error _ => false
      | .ok (valAtZero, steps) =>
        valAtZero = 10 ∧ steps == [
          { step := 30, num := 2 : Core.APPair },
          { step := 10, num := 3 : Core.APPair }
        ]

/-
# Implement Advanced tensor indexing.

https://numpy.org/doc/stable/user/basics.indexing.html#advanced-indexing

Given tensors ind_1, ind_2, ..., x[ind_1, ind_2, .., ind_N] has advanced
indexing over the elements of x.
The result of the access is:

result[i_1, ..., i_M] == x[ind_1[i_1, ..., i_M], ind_2[i_1, ..., i_M],
                          ..., ind_N[i_1, ..., i_M]]

In NumPy, mixing advanced indexing and basic indexing is allowed. However,
in NKI, only one of the two forms is allowed.
Refer to:
https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/programming_model.html
"Note that currently NKI does not support mixing Basic and Advanced Tensor
  Indexing in the same Index tuple."

## Q: Is the result of advanced indexing a view of the tensor or a copy of it?
In the case of numpy, the numpy doc above says that advanced indexing always
returns a copy of the data (contrast with basic slicing that returns a view).
However, we cannot assume the same thing for NKI, because NKI typically does
the following stuff (excerpted from a matmul example):

  i_lhsT_p, i_lhsT_f = nl.mgrid[0:128, 0:64]
  ...
  nl.store(result[i_out_p, i_out_f], value=result_sbuf)
           ^^^^^^^^^^^^^^^^^^^^^^^^
           this is doing advanced indexing.

If advanced indexing returns a copy of the view, the store statement does not
make sense. Therefore, advanced indexing in NKI must have view semantics.
-/
def advancedAccessPattern (tensor : Core.TensorName) : Term -> Err Core.AccessPattern
  | .tuple l | .list l => mkAccessPattern tensor l
  | t => mkAccessPattern tensor [t]
where
  mkAccessPattern (tensor : Core.TensorName) (inds: List Term) : Err Core.AccessPattern
  := do
    let sizes := tensor.shape.toList
    if sizes.length ≠ inds.length
    then throw "unimplemented: number of dimensions mismatch"
    else if sizes.isEmpty
    then throw "empty indices"
    else
      -- numElems[i] = sizes[i] * sizes[i+1] * ... * sizes[-1]
      -- numElems[sizes.length] = 1
      let numElems := sizes.foldr (fun sz l => match l with
        | [] => [sz]
        | h::l' => (sz*h)::h::l') [1]
      -- The goal is to build AccessPattern that does the following:
      -- result[i_1, ..., i_M] == x[ind_1[i_1, ..., i_M], ind_2[i_1, ..., i_M],
      --                        ..., ind_N[i_1, ..., i_M]]
      let mut accessPatterns : List Core.AccessPattern := []
      for inds_i in inds do
        match inds_i with
        | .tensor t =>
          -- Create AccessPattern for each ind_j.
          let (valAtZero, steps) <- decomposeLinearIntTensor t
          -- To create AccessPattern, freePattern's steps must be
          -- multiplied by the number of elements in the lower dimensions.
          -- For example, if tensor t has 3x4, t[i,j] is t[i * 4 + j]
          let steps: List Core.APPair := List.map
            (fun (ap,i) =>
                { step := ap.step * Int.ofNat (numElems.getD (i+1) 1),
                  num := ap.num })
            (steps.zipIdx)
          accessPatterns := accessPatterns ++ [{
            tensor := tensor,
            parNum := 1, -- This will be filled later.
            freePattern := steps,
            offset := Int.toNat valAtZero
          }]
        | _ => throw "NKI doesn't allow mixing tensor index + basic index"
      -- Accumulate AccessPattern of ind_js and create one large AccessPattern
      match accessPatterns with
      | pat1::pat' =>
        let mut res : Core.AccessPattern := pat1
        for ap in pat' do
          let mut fp: List Core.APPair := []
          for (p1,p2) in (List.zip res.freePattern ap.freePattern) do
            if p1.num ≠ p2.num then
              throw "APPair num mismatch"
            else
              fp := fp ++ [{
                step := p1.step + p2.step,
                num := p1.num
              }]
          res := {
            tensor := res.tensor,
            parNum := res.parNum,
            freePattern := fp,
            offset := res.offset }
        -- Check the partition index & fill in the partition number
        match res.freePattern with
        | fp0::fp' =>
          let numPartitions := fp0.num
          if not (fp0.step = numElems.getD 1 0)
          then throw "nontrivial step for partition index"
          else return {
            tensor := res.tensor,
            parNum := numPartitions,
            freePattern := fp',
            offset := res.offset
          }
        | _ => throw "insufficient indices"
      | _ => throw "insufficient indices"


#guard
  match do
    let shape <- Core.Shape.fromList [/-parnum-/2,3,4]
    Core.TensorName.make "x" Core.Dtype.int8 shape none with
  | .ok (tensor:Core.TensorName) =>
    let mk (ls:List Int): TensorLib.Tensor :=
      let t := TensorLib.Tensor.ofIntList! TensorLib.Dtype.int64 ls
      let t3d := t.reshape! (TensorLib.Shape.mk [2,3,4])
      t3d
    -- a,b,c = numpy.mgrid[0:2,0:3,0:4]
    let a : Term := .tensor (mk [
      0,0,0,0, 0,0,0,0, 0,0,0,0,
      1,1,1,1, 1,1,1,1, 1,1,1,1])
    let b : Term := .tensor (mk [
      0,0,0,0, 1,1,1,1, 2,2,2,2,
      0,0,0,0, 1,1,1,1, 2,2,2,2
    ])
    let c : Term := .tensor (mk [
      0,1,2,3, 0,1,2,3, 0,1,2,3,
      0,1,2,3, 0,1,2,3, 0,1,2,3,
    ])
    let res := advancedAccessPattern tensor (.tuple [a,b,c])
    res == .ok
      (Core.AccessPattern.mk tensor 2 [
        { step := 4, num := 3},
        { step := 1, num := 4},
      ] 0)
  | .error _ => false

/-
Access to pointer types (a.k.a. Address)
NKI users can define memory regions by using slices on other memory regions.
Initially, the regions `sbuf` and `psum` are defined. For example:

  ptr = sbuf[0:32, 0:512]  # memory region in SBUF
  ptr2 = ptr[:, :256]      # left half of region
  ptr3 = ptr[:, 256:]      # right half of region

https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/nki_arch_guides.html
-/

def pointerAccess (addr : Core.Address) (i : Term) : Err Term := do
  let chkPdim (p : Nat) : Err Nat := do
    if p != 0 && p != 32 && p != 64 && p != 96 then
      throw "partition dimension must be 0, 32, 64, or 96"
    if p > addr.size.fst then
      throw s!"partition dimension {p} is larger than the pointer size {addr.size.fst}"
    return p

  let chkFdim (f : Nat) : Err Nat := do
    if f < 0 then
      throw s!"free dimension {f} must be positive"
    if f % 2 != 0 then
      throw s!"free dimension {f} must be even"
    if f > addr.size.snd then
      throw s!"free dimension {f} is larger than pointer size {addr.size.snd}"
    return f

  let chkPslice (s : Slice) : Err (Option Nat × Nat) := do
    if s.u < 0 then
      throw s!"partition size {s.u} must be positive"
    if s.u > addr.size.fst then
      throw s!"partition size {s.u} is larger than the pointer size {addr.size.fst}"
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

  let ptr (partitionOffset freeOffset : Option Nat) (size : Nat × Nat) : Term :=
    .pointer { memory := addr.memory
               size
               partitionOffset,
               freeOffset,
               parent := addr
             }

  match <- termToIndex [addr.size.fst, addr.size.snd] i with
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

-- Top-level subscript access t[i]
-- TODO: add case for String
def access (t : Term) (i : Term) : Err Term := do
  match t with
  | .module _
  | .builtin ..
  | .source _
  | .none
  | .ellipsis
  | .slice ..
  | .store .. => throw "subscript not supported"
  | .string _ => throw "string subscript not implemented"
  | .tensor _ => throw "subscript of a constant tensor unimplemented"
  | .tuple l => listAccess "list" l i
  | .list l => listAccess "tuple" l i
  | .pointer addr => pointerAccess addr i
  | .mgrid => do
      let slice_convert (s:Term): Err TensorLib.Slice :=
        match s with
        | .slice b e st => TensorLib.Slice.make b e st
        | _ => throw "not .slice"
      let slices : List TensorLib.Slice <-
        List.mapM slice_convert (match i with
        | .tuple l => l | t => [t])
      -- Use TensorLib's mgrid semantics. Thus this naturally picks NumPy's
      -- mgrid semantics, whose return type (ndarray) is slightly different
      -- from NKI''s mgrid return type. The usages of NKI API are designed to be
      -- analogous to that of NumPy API anyway.
      let res <- TensorLib.mgrid slices
      -- Note: this does not support '.p' and '.x' in NKI because a generic
      -- tensor does not have such fields.
      return .tensor res
  | .expr .. => do
      let tensor : Core.TensorName <- fromNKI? t
      -- Try basic indexing first
      tryCatch
         (do
          let indices <- termToIndex tensor.shape.toList i
          let access <- Core.Access.mkBasic tensor indices
          let shape <- Tensor.inferShape access
          return .expr (.value (.access access)) (.tensor tensor.dtype shape))
         (fun _ => do
          -- Try advanced indexing
          let ap <- advancedAccessPattern tensor i
          let access := Core.Access.pattern ap
          let shape <- Tensor.inferShape access
          return .expr (.value (.access access)) (.tensor tensor.dtype shape))


--
/-
# Handling of assignment statements

Assignments can be things like:

  x = y = 1
  a, y = (1,2)

or even

  (x,y), z = a, [b,c] = f()

The current implementation requires that these kinds of complex assignments are
expanded at tracing time. That is, in the example above the call to f must
generate a tuple or list of the right size at tracing time. This will then be
expanded out to assignments of the individual variables.

In general, we need to make sure the right-hand side is only evaluated once. For
example, consider the assignment below:

  (x,y) = a = (f(), 1)

The following is and incorrect translation, because f is called twice.

  a = (f(), 1)
  x = f()  # INCORRECT
  y = 1

One correct translation is:

  tmp = f()
  a = (tmp, 1)
  x = tmp
  y = 1

The extra variable `tmp` is only needed if the right-hand side has side-effects
or is expensive to compute. Otherwise, it is safe to copy the right-hand side
everywhere it is needed.

In the above case, only the first assignment is emitted to the translated
function. The other three assignments are placed in the environment, but not
emitted. Therefore any uses of a, x, or y will be replaced with their
assignments. This is effectively a simple form of constant propagation and
dead-code elimination for simple assignments.
-/

-- Convert an expression in assignment context (an L-Value).
-- TODO: handle subscript
partial def LValue (e : Expr) : Trace Term :=
  withPos e.pos (lval e.expr)
where
  lval : Expr' -> Trace Term
  | .name id .store => return .expr (.value $ .var id) (.obj "object".toName)
  | .attr _ id .store => throw s!"cannot assign to attribute {id}"
  | .tuple es .store => return .tuple (<- es.attach.mapM fun ⟨ e, _ ⟩ => LValue e)
  | .list es .store => return .list (<- es.attach.mapM fun ⟨ e, _ ⟩ => LValue e)
  | .subscript _ _ .store => throw "unimp subscript store"
  | _ => throw "cannot assign to expression"

-- Convert an R-Value to a pure expression, emitting
-- additional assignments as needed.
def RValue : Term -> Trace Term
  | .module n => return .module n
  | .builtin n t s => return .builtin n t s
  | .source f => return .source f
  | .none => return .none
  | .string s => return .string s
  | .tensor t => return .tensor t
  | .tuple es => return .tuple (<- es.attach.mapM fun ⟨ e, _ ⟩ => RValue e)
  | .list es => return .tuple (<- es.attach.mapM fun ⟨ e, _ ⟩ => RValue e)
  | .ellipsis => return .ellipsis
  | .slice a b c => return .slice a b c
  | .store acc op args => do
       add_stmt (.store acc op args)
       let shape <- Tensor.inferShape acc
       return .expr (.value (.access acc)) (.tensor acc.tensor.dtype shape)
  | .pointer a => return .pointer a
  | .expr e@(.call ..) ty => do
       let v := (<- genName).toString
       add_stmt (.assign v e)
       return .expr (.value $ .var v) ty
  | .expr e ty => return .expr e ty
  | .mgrid =>
      -- Assume that people do not write a code that has mgrid appearing solely
      -- without a subscript on the RHS of assignment...
      throw "unimplemented"

-- Create an assignment to a Core Expr, this must be a variable
def assignExpr (e : Core.Expr) (t : Term) : Trace Unit := do
  match e with
  | .value (.var x) => extend x.toName t
  | _ => throw s!"cannot assign to {repr e}"

-- Unpack an RValue, must be a list or tuple
def unpack : Term -> Trace (List Term)
  | .tuple l | .list  l => return l
  | .tensor t =>
    -- Unpack tensor to a list of subtensors
    match t.shape.val with
    | [] => return []
    | nTensors::shapes' =>
      -- Make a tuple whose number of element is n_tensors
      let newShape := TensorLib.Shape.mk shapes'
      -- `extract i` returns the subtensor t[i].
      let extract (i:Nat): Trace Term := do
        if t.startIndex ≠ 0 ∨ t.unitStrides ≠ t.shape.unitStrides then
          throw "Don't know how to extract i'th subarray of t"
        else
          let subtensorSz := t.size / nTensors
          let extractedData := t.data.extract (subtensorSz * i * t.itemsize)
              (subtensorSz * t.itemsize)
          return .tensor ({
            dtype := t.dtype,
            shape := newShape,
            data := extractedData
            : TensorLib.Tensor
          })

      (List.range nTensors).mapM extract

  | t => throw s!"cannot unpack non-iterable object {repr t}"

-- Assign to a term, handling unpacking for tuples and lists
def assignTerm (x : Term) (e : Term) : Trace Unit := do
  match x with
  | .module name => throw s!"cannot assign to {name}"
  | .mgrid => throw s!"cannot assign to mgrid"
  | .builtin name .. => throw s!"cannot assign to {name}"
  | .source _ => throw "cannot assign to function"
  | .none => throw "cannot assign to None"
  | .string _ => throw "cannot assign to a string literal"
  | .tensor _ => throw "cannot assign to a constant tensor"
  | .tuple l
  | .list  l  => assignList l (<- unpack e)
  | .ellipsis => throw "cannot assign to ellipsis"
  | .slice .. => throw "cannot assign to slice"
  | .store .. => throw "cannot assign to a store"
  | .pointer .. => throw "cannot assign to a pointer"
  | .expr x _ => assignExpr x e
where
  assignList : List Term -> List Term -> Trace Unit
  | [], [] => return ()
  | [], _  => throw "not enough values to unpack"
  | _, []  => throw "too many values to unpack"
  | x::xs, t::ts => do
      assignTerm x t;
      assignList xs ts

-- Top-level assignment handling
-- e.g. x1 = x2 = e
def assign (xs : List Expr) (e : Term) : Trace Unit := do
  let xs <- xs.mapM LValue
  let e <- RValue e
  for x in xs do
    assignTerm x e

-- Translation of for-loop iterators

-- range, but only in a for-loop context
private def range (start stop step : Int) : List Term :=
  let int i := Term.expr (.value (.int i)) .int
  if step = 0 then []
  else if 0 < step then
    if stop <= start then [] else
    if stop <= start + step then [int start] else
    int start :: range (start + step) stop step
  else -- step < 0
    if start <= stop then [] else
    if start + step <= stop then [int start] else
    int start :: range (start + step) stop step
termination_by (stop - start).natAbs

def termToIter : Term -> Err (List Term)
  | .tuple l | .list l => return l
  | .expr (.call "range" l _) _ =>
      match l with
      | [ .int e ] => return (range 0 e 1)
      | [ .int s, .int e ] => return (range s e 1)
      | [ .int s, .int e, .int t ] =>
          if t == 0
          then throw "range arg 3 must not be zero"
          else return (range s e t)
      | _ => throw "invalid argument to range"
  | .expr (.call "nki.language.affine_range" l _) _ =>
      -- Must behave equally to the simple sequential loop.
      match l with
      | [ .int e ] => return (range 0 e 1)
      | _ => throw "invalid argument to nki.language.affine_range"
  | _ => throw "unsupported loop iterator"

/-
# Expressions and Statements
-/

-- return type of statement evaluator (see stmt below)
inductive StmtResult where
  | done | brk | cont | ret (t : Term)
  deriving Repr, BEq

mutual

partial def expr [FromNKI a] (e : Expr) : Trace a :=
  withPos e.pos do fromNKI? (<- expr' e.expr)

-- This is only used for slices
partial def integer? : Option Expr -> Trace (Option Int)
  | none => return none
  | some e => expr e

partial def expr' : Expr' -> Trace Term
  | .const c => return const c
  | .tensor s dty => do
      let shape <- s.mapM expr
      let shape <- Core.Shape.fromList shape
      let name <- genName "t".toName
      let dtype <- fromNKI? (.expr (.value $ .var dty) .none)
      let tensor <- Core.TensorName.make name.toString dtype shape none
      return .expr (.value $ .access $ .simple tensor) (.tensor dtype shape)
  | .name id _ => lookup id.toName
  | .attr e id _ => do ((<- expr e : Term).attr id)
  | .tuple l _ => return .tuple (<- l.mapM expr)
  | .list  l _ => return .list  (<- l.mapM expr)
  | .subscript t i _ => do access (<- expr t) (<- expr i)
  | .slice x y z => return .slice (<- integer? x) (<- integer? y) (<- integer? z)
  | .boolOp op xs => do boolOp op (<- xs.mapM expr)
  | .binOp op l r => do binOp op (<- expr l) (<- expr r)
  | .unaryOp op e => do unOp op (<- expr e)
  | .compare l ops cs => do compare (<- expr l) ops (<- cs.mapM expr)
  | .ifExp tst tru fls => do
      let tst <- (<- expr tst : Term).isTrue
      let tru <- expr tru  -- eagerly evaluate both branches
      let fls <- expr fls  -- to report errors to user
      return if tst then tru else fls
  | .call f args kws => do
      match (<- expr f : Term) with
      | .builtin n _ self => do
          let f <- builtinFn n
          let args <- args.mapM expr
          let kwargs <- kws.mapM (keyword expr)
          let args := match self with
                      | none => args
                      | some t => t :: args
          f args kwargs
      | .source f    => do function_call f (<- args.mapM expr) (<- kws.mapM (keyword expr))
      | .expr (.value (.var f)) _ =>
          return .expr (.call f (<- args.mapM expr) (<- kws.mapM (keyword expr))) default
      | _ => throw "not a callable type"

partial def keyword (f : Expr -> Trace a) : Keyword -> Trace (String × a)
  | ⟨ id, e, p ⟩ => withPos p do return (id, (<- f e))

partial def stmt : Stmt -> Trace StmtResult
  | ⟨ s', p ⟩ => withPos p (stmt' s')

partial def stmt' : Stmt' -> Trace StmtResult
  | .pass => return .done
  | .ret e => do
      let t <- expr e
      let t <- RValue t
      return .ret t
  | .expr e => do
      let t <- expr e
      let _ <- RValue t
      return .done
  | .assert e => do
      let t : Term <- expr e
      if (<- t.isFalse) then throw "assertion failed"
      return .done
  | .assign xs e => do assign xs (<- expr e); return .done
  | .augAssign x op e => do assign [x] (<- expr' (.binOp op x e)); return .done
  | .annAssign _ _ .none => return .done
  | .annAssign x _ (.some e) => do assign [x] (<- expr e); return .done
  | .ifStm e thn els => do
      let t : Term <- expr e
      let body := if <- t.isTrue then thn else els
      stmts body
  | .forLoop x iter body orelse => do
      let x <- LValue x
      let iter <- expr iter
      let ts <- termToIter iter
      for t in ts do
        assignTerm x t
        let res <- stmts body
        if res == .cont then continue
        if res == .brk then break
        if let .ret _ := res then return res
      stmts orelse
  | .breakLoop => return .brk
  | .continueLoop => return .cont

partial def stmts : List Stmt -> Trace StmtResult
  | [] => return .done
  | s :: l => do
      match <- stmt s with
      | .done => stmts l
      | r => return r

-- Bind positional and keyword arguments to a Python function based on its
-- signature.

partial def bind_args (f : Fun)
                      (args : List Term)
                      (kwargs : List (String × Term))
                      (rename : Bool := false)
                      : Trace (List (String × Term)) := do
  if f.args.vararg != none || f.args.kwarg != none then
    throw "var args not supported"
  if args.length < f.args.posonlyargs.length then
    throw "not enough arguments"
  let dflts := f.args.all_defaults
  let names := f.args.names
  if args.length + kwargs.length > names.length then
    throw "too many arguments supplied (varargs not supported)"
  let argmap <- f.args.names.zipIdx.mapM fun (x, i) => do
    if h:args.length > i then
      return (x, args.get (Fin.mk i h))
    else if let some v := kwargs.lookup x then
      return (x, v)
    else if let some kw := dflts.find? fun k => k.id == x then
      return (x, <- expr kw.value)
    else
      throw s!"argument {x} not supplied"
  -- rename tensors if asked to
  let argmap <- if rename then argmap.mapM renameTensors else pure argmap
  return argmap
where
  renameTensors : String × Term -> Trace (String × Term)
  | (s, .expr (.value (.access a)) ty) =>
      return (s, .expr (.value (.access (<- renameAcc s a))) ty)
  | other => return other
  renameAcc (s : String) : Core.Access -> Err Core.Access
  | .simple t => return .simple (renameTN s t)
  | .basic { tensor, indexes, .. } => Core.Access.mkBasic (renameTN s tensor) indexes
  | .pattern ap => return .pattern { ap with tensor := renameTN s ap.tensor }
  renameTN (s : String) (t : Core.TensorName) : Core.TensorName := { t with name := s }

/-
Function calls are split into two parts because we need to handle the top-level
kernel function differently: its argument tensors will be inputs, but internal
function call arguments will not be input tensors.
-/
partial def call (f : Fun)
                 (args : List (String × Term))
                 : Trace Term := do
  withSrc f.line f.source $ enterFun $ do
    args.forM fun (x,e) => do extend x.toName e
    match <- stmts f.body with
    | .ret t => return t
    | _ => return .none

partial def function_call (f : Fun)
                          (args : List Term)
                          (kwargs : List (String × Term))
                          : Trace Term := do
  let args <- bind_args f args kwargs (rename:=false)
  call f args

end

/-
Evaluate each global in the current environment, skipping any globals that are
already defined. We do not redefine globals, because we may have picked up
functions with dummy implementations, e.g., nki.language.add is defined as:

  def add(x,y): pass

in the official NKI API. We do not want this to shadow the built-in definition
of add, if we have one. If we have an internal definition, we will use this
over anything found during parsing.
-/
private def globals (k : Kernel) : Trace Unit := do
  let s <- get
  for f in k.funcs do
    let n := f.name.toName
    if not (s.globals.contains n) then
      extend_global n (.source f)
  for g in k.globals do
    let n := g.id
    let name := n.toName
    if not (s.globals.contains name) then
      if not (k.undefinedSymbols.contains n) then
        extend_global name (<- expr' g.value.expr)

/-
Check all of the undefined names against the global environment. If an
undefined name has a builtin implementation, then it is OK. In
addition, we allow undefined names in certain special modules. This is
because, for certain modules, we want to pass anything we don't know
about through to KLR. For example, if NKI creates a new experimental
api `nki.isa.newfn`, then rather than generating an error, a call to
this function will end up in the KLR:

  x[...] = nki.isa.newfn(t, 3)

  .store (.access x ...)
    .call (.var "nki.isa.newfn") [t, .const 3] ...

Of course, the compiler will then fail, not knowing how to translate
this constant. However, you still get out a KLR artifact that some
other, experimental compiler may be able to handle.
-/
def undefinedOK : Name -> Bool
  | .str .anonymous "nki" => true
  | .str n _ => undefinedOK n
  | _ => false

def checkUndefined (k : Kernel) : Trace Unit := do
  let mut undefined := []
  for sym in k.undefinedSymbols do
    let name := sym.toName
    if (<- lookup_global? name).isNone then
      if undefinedOK name then do
        warn s!"unknown NKI API {name}"
        extend_global name (.expr (.value $ .var name.toString) (.obj name))
      else
        undefined := name :: undefined
  if undefined.length > 0 then
    throw s!"undefined names {undefined}"

-- Call the top-level kernel function
def traceKernel (k : Kernel) : Trace Core.Kernel := do
  globals k
  checkUndefined k
  match k.funcs.find? fun f => f.name == k.entry with
  | none => throw s!"function {k.entry} not found"
  | some f => do
      let args <- k.args.mapM expr
      let kwargs <- k.kwargs.mapM fun kw => return (kw.id, <- expr kw.value)
      let args <- bind_args f args kwargs (rename := true)
      let res <- call f args
      let inputs := tensors (args.map fun x => x.snd)
      let outputs := tensors res
      return {
        name := k.entry
        inputs := inputs
        outputs := outputs
        body := (<- get).body.toList
      }
