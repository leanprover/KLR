/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.Memory
import TensorLib.Iterator

class Encodable (dsize : Nat) (α β : Type _) where
  read : Vector α dsize → Option β
  write : β → Vector α dsize
  read_write : (read v).map write = .none ∨ (read v).map write = .some v
  write_read : read (write b) = .some b

def Dtype.interp {DataT : Type _} : KLR.Core.Dtype → Type
| .uint64   => UInt64
| .uint32   => UInt32
| .uint16   => UInt16
| .uint8    => UInt8
| .int64    => Int64
| .int32    => Int32
| .int16    => Int16
| .int8     => Int8
| .float16 | .float32r | .float32 | .float8e5 | .float8e4 | .float8e3 | .bfloat16 => DataT


namespace NML

/-
# NML, Neuron Modeling Language

Plan:
The language contains a subset that is similar to the ISA, but abstracts over the lowest-level details.
The langauge contains a subset similar to some of the higher-level operators akin to KLR, or `nki.language`.
Finally, it contains ghost operations that are purely logical and have no concrete meaning in either
language, such as the unbounded allocation operator.
Like several other relational logics, this setup allows users to prove chains of equivalences where
the intermediate programs are not constrained to any individual language.
For us, this is enabled by the fact that all of our languages are very similar, and can all fit into a single
operational semantics.

The language is parameterized by a type of floating point numbers, see `KLR/Semantics/Float.lean` -/

variable {DataT : Type _}

open KLR.Core TensorLib

def Dtype.interp : Dtype → Type _
| .uint64   => UInt64
| .uint32   => UInt32
| .uint16   => UInt16
| .uint8    => UInt8
| .int64    => Int64
| .int32    => Int32
| .int16    => Int16
| .int8     => Int8
| .float16 | .float32r | .float32 | .float8e5
| .float8e4 | .float8e3 | .bfloat16 => DataT

/-- A pointer to a tensor that carries additional metadata. -/
structure TensorHandle extends KLR.Core.TensorName where
  /-- Interpret vectors of store-level indicies into -/
  [encoding : Encodable dtype.size UInt8 (Dtype.interp (DataT := DataT) dtype) ]
  /-- Where the tensor is being stored in our memory model -/
  index : KLR.Core.DualMemoryStoreIndex UInt8
  /-- Multiaffine equation mapping tensor indices to Address indices (not physical)! -/
  layout : AffineMap

def TensorHandle.hbm_index? (r : @TensorHandle DataT) : Option Nat :=
  match r.index with
  | .in_bounded => .none
  | .in_unbounded i => .some i

-- DualMemory.in_memory
def TensorHandle.get_store? (r : @TensorHandle DataT) (m : NeuronMemory) : Option (LocalStore UInt8) :=
  match r.address.memory, r.index with
  | .hbm, .in_bounded => .none
  | .hbm, .in_unbounded i => m.hbm[i]?
  | .sbuf, .in_bounded => .some m.sbuf.bounded.toLocalStore
  | .sbuf, .in_unbounded i => m.sbuf.unbounded[i]?
  | .pmem, _ => .none
  | .reg, _ => .none


def TensorHandle.upd_store? (r : @TensorHandle DataT) (m : NeuronMemory) (L : LocalStore UInt8 → LocalStore UInt8) :
    Option NeuronMemory :=
  match r.address.memory, r.index with
  | .hbm, .in_bounded => .none
  | .hbm, .in_unbounded i => do
      let x ← m.hbm[i]?
      return { m with hbm := m.hbm }
  | .sbuf, .in_bounded =>
      sorry
      -- .some { m with sbuf := L m.sbuf.bounded.toLocalStore }
  | .sbuf, .in_unbounded i =>
      sorry -- m.sbuf.unbounded[i]?
  | .pmem, _ => .none
  | .reg, _ => .none




/-- NML values. These are fully-reduced expressions. -/
inductive Value
| unit
| bool     (_ : Bool)
| data     (_ : DataT)
| int      (_ : Int)
| linfunc  (_ : AffineMap)
| ptr      (_ : TensorHandle (DataT:=DataT))

def Value.as_handle? : @Value DataT → Option (@TensorHandle DataT) | .ptr t => .some t | _ => .none

/-- NML expressions. These are terms which reduce to a value and possibly update the state.
There is no control flow inside expressions. -/
inductive Expr
| val           (_ : @Value DataT)
| var           (_ : String)
| load          (_ : AffineMap) (_ : Expr)
| store         (src : Expr) (_ : AffineMap) (dst : Expr)
| unary_scalar  (_ : Expr) (_ : DataT → DataT)

abbrev Expr.pure? : @Expr DataT → Prop
| .val _ | .var _ => True
| _ => False

structure PureExpr where
  expr : @Expr DataT
  pure : Expr.pure? expr

/-- NML statements. Control flow lives here. -/
inductive Stmt
| ret     (_ : @Expr DataT)
| assign  (_ : Option String) (_ : @Expr DataT)
| loop    (I : Type _) [Iterator I (@Value DataT)] (_ : String) (_ : Option I) (body : List Stmt)

abbrev Locals := String → Option (@Value DataT)

structure State where
  memory : KLR.Core.NeuronMemory
  locals : @Locals DataT

def Locals.bind (s : @Locals DataT) (x : String) (v : @Value DataT) : @Locals DataT:=
  fun x' => if x = x' then .some v else s x'

/-- The state of execution of the program. -/
inductive ExecState where
| run   (_ : List (@Stmt DataT)) (_ : @State DataT)
| done  (_ : @Value DataT)

/-- Language of expressions.

This is different from KLR's expression lanaguge currently, the semantics should be able to
express something like `nki.load` which is an effectful call that also returns a python-level value. -/
inductive ExprStep : @Expr DataT → @State DataT → @Value DataT → KLR.Core.NeuronMemory → Type _ where
/-- [value] -/
| value :
    ExprStep (.val v) s v s.memory
/-- [variable] -/
| var :
    s.locals x = .some v →
    ExprStep (.var x) s v s.memory
/-- [Non-sized, full, load] Load a HBM tile to a SBUF tile. Return a pointer to the new tile. Similar to nki.load.
For now, only support trivial indexing.
  - Evaluate the location expression to a tensor pointer in hbm
  - Copy the hbm tensor data to a new unbounded tile in sbuf
  - Return the tensor pointer, modified to point at the new sbuf tile -/
| load_full :
    AffineMap.is_trivial asn →
    ExprStep e s (.ptr tensor) s' →
    tensor.address.memory = KLR.Core.Memory.hbm →
    tensor.hbm_index? = .some raw_index →
    (_ : i < s'.hbm.size) →
    ExprStep (.load asn e) s
      (.ptr {tensor with address.memory := .sbuf, index := .in_unbounded s'.sbuf.unbounded.size})
      { s' with sbuf.unbounded := s'.sbuf.unbounded.push s'.hbm[i] }
/-- [Non-sized, full, store] Store a SBUF tile to HBM. Similar to nki.store. -/
| store_full :
    AffineMap.is_trivial asn →
    ExprStep e1 s0 (.ptr sbuf_tensor) s1 →
    sbuf_tensor.address.memory = KLR.Core.Memory.sbuf →
    (H : DualMemory.in_memory s2.sbuf sbuf_tensor.index) →
    ExprStep e2 ⟨s1, s0.locals⟩ (.ptr hbm_tensor) s2 →
    hbm_tensor.address.memory = KLR.Core.Memory.hbm →
    hbm_tensor.hbm_index? = .some raw_index →
    (_ : i < s2.hbm.size) →
    ExprStep (.store e1 asn e2) s0 .unit
      { s2 with hbm[i] :=
          ⟨ fun (p, f) =>
              let L := (s2.sbuf.get_store sbuf_tensor.index H)
              L.get (p + sbuf_tensor.address.partitionOffset.getD 0,
                     f + sbuf_tensor.address.freeOffset.getD 0)⟩ }
/-- [unary scalar] Idealized pure function application to a tensor, in-place.
Returns the address of the tensor. -/
| unary_scalar :
    ExprStep e s0 (.ptr tensor) s1 →
    -- tensor.get_store? s1 = .some L →
    tensor.upd_store? s1 sorry = .some s2 →
    ExprStep (.unary_scalar e f) s0 (.ptr tensor) s2

-- TODO: Refactor this file to a proper small-step form
-- TODO: Small step semantics with early return in loops? Model termination w/ ExecState (like a Monad)
-- TODO: Write an interpreter and prove it correct. Use a nondeterminism monad.

abbrev Pgm := List (@Stmt DataT)
abbrev Cfg := @Pgm DataT × @State DataT

inductive MultiStep : List (@Stmt DataT) → @State DataT → @ExecState DataT → Type _ where
/-- [ Early return ] Step into the .done state using .ret at any time -/
| ret :
    ExprStep e s v _ →
    MultiStep (.cons (.ret e) ps) s (.done v)
/-- [ Assignment ] Expression evaluates first, with effects. -/
| asn :
    ExprStep e s v s' →
    MultiStep p ⟨s', s.locals.bind x v⟩ r →
    MultiStep (.cons (.assign (.some x) e) p) s r
/-- [ Sequencing ] Evaluate expression but don't bind the result a variable -/
| seq :
    ExprStep e s _ s' →
    MultiStep p ⟨s', s.locals⟩ r →
    MultiStep (.cons (.assign .none e) p) s r
/-- [ Loop termination ] Loops continue onwards if their iterator is done. -/
| loop_exit {I : Type _} [Iterator I (@Value DataT)] :
    MultiStep p s r →
    MultiStep (.cons (.loop I _ .none _) p) s r
/-- [ Loop eary return ] If loop is not terminated, and body executes to .done, terminate. -/
| loop_early {I : Type _} [Iterator I (@Value DataT)] (i i' : I) :
    MultiStep body ⟨s.memory, s.locals.bind x (Iterator.peek i)⟩ (.done r) →
    MultiStep (.cons (.loop I x (.some i) body) p) s (.done r)
/-- [ Loop iterate ] If loop is not terminated, and body executes to a running state,
the program setps to a loop with iterator.next (lexical scope + effects). -/
| loop_continue {I : Type _} [Iterator I (@Value DataT)] (i i' : I) :
    MultiStep body ⟨s.memory, s.locals.bind x (Iterator.peek i)⟩ (.run [] s') →
    MultiStep (.cons (.loop I x (Iterator.next (@Value DataT) i) body) p) ⟨s'.memory, s.locals⟩ r →
    MultiStep (.cons (.loop I x i body) p) s r

end NML
