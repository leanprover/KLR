/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.Memory
import KLR.Semantics.SmallStep
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

open KLR.Core TensorLib

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


variable (DataT : Type _)

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

def lift_encoding_to_store (f : DataT → DataT) : LocalStore UInt8 → LocalStore UInt8 :=
  sorry

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

def Expr.is_value? : Expr DataT → Prop | .val _ => True | _ => False

abbrev Expr.pure? : @Expr DataT → Prop
| .val _ | .var _ => True
| _ => False

structure PureExpr where
  expr : @Expr DataT
  pure : Expr.pure? DataT expr

/-- NML statements. Control flow lives here. -/
inductive Stmt
| ret       (_ : @Expr DataT)
| assign    (_ : Option String) (_ : @Expr DataT)
| loop      (I : Type _) [Iterator I (@Value DataT)] (_ : String) (_ : Option I) (body : List Stmt)

structure State where
  memory : KLR.Core.NeuronMemory

abbrev Locals := String → Option (@Value DataT)

def Locals.bind (s : @Locals DataT) (x : String) (v : @Value DataT) : @Locals DataT :=
  fun x' => if x = x' then .some v else s x'

-- Allows us to write a lexically-scoped small-step semantics
structure Task where
  stmt : Stmt DataT
  env : Locals DataT


def Task.bind (T : Task DataT) (x : String) (v : Value DataT) : Task DataT := sorry

inductive ExecState where
| run   (_ : List (Task DataT))
| done  (_ : Value DataT)

/-- Expressions semantics -/
inductive ExprStep : Expr DataT → Locals DataT → State → Value DataT → State → Type _ where
/-- [value] -/
| value :
    ExprStep (.val v) loc st v st
/-- [variable] -/
| var :
    loc x = .some v →
    ExprStep (.var x) loc st v st
/-- [Non-sized, full, load] Load a HBM tile to a SBUF tile. Return a pointer to the new tile. Similar to nki.load.
For now, only support trivial indexing.
  - Evaluate the location expression to a tensor pointer in hbm
  - Copy the hbm tensor data to a new unbounded tile in sbuf
  - Return the tensor pointer, modified to point at the new sbuf tile -/
| load_full :
    AffineMap.is_trivial asn →
    ExprStep e loc st (.ptr tensor) st' →
    tensor.address.memory = KLR.Core.Memory.hbm →
    tensor.hbm_index? = .some raw_index →
    (_ : i < st'.memory.hbm.size) →
    ExprStep (.load asn e) loc st
      (.ptr {tensor with address.memory := .sbuf, index := .in_unbounded st'.memory.sbuf.unbounded.size})
      { st' with memory.sbuf.unbounded := st'.memory.sbuf.unbounded.push st'.memory.hbm[i] }
/-- [Non-sized, full, store] Store a SBUF tile to HBM. Similar to nki.store. -/
| store_full :
    AffineMap.is_trivial asn →
    ExprStep e1 loc s0 (.ptr sbuf_tensor) s1 →
    sbuf_tensor.address.memory = KLR.Core.Memory.sbuf →
    (H : DualMemory.in_memory s2.memory.sbuf sbuf_tensor.index) →
    ExprStep e2 loc s1 (.ptr hbm_tensor) s2 →
    hbm_tensor.address.memory = KLR.Core.Memory.hbm →
    hbm_tensor.hbm_index? = .some raw_index →
    (_ : i < s2.memory.hbm.size) →
    ExprStep (.store e1 asn e2) loc s0 .unit
      { s2 with memory.hbm[i] :=
          ⟨ fun (p, f) =>
              let L := (s2.memory.sbuf.get_store sbuf_tensor.index H)
              L.get (p + sbuf_tensor.address.partitionOffset.getD 0,
                     f + sbuf_tensor.address.freeOffset.getD 0)⟩ }
-- /-- [unary scalar] Idealized pure function application to a tensor, in-place.
-- Returns the address of the tensor. -/
| unary_scalar :
    ExprStep e l0 s0 (.ptr tensor) s1 →
    tensor.upd_store? DataT s1.memory (lift_encoding_to_store DataT f) = .some s2 →
    ExprStep (.unary_scalar e f) l0 s0 (.ptr tensor) { s1 with memory := s2 }

inductive step : ExecState DataT × State → ExecState DataT × State → Prop where
/-- [ Return ] -/
| ret :
    ExprStep DataT e loc s v s' →
    step (.run <| .cons ⟨.ret e, loc⟩ ps, s) (.done v, s')
/-- [ Assignment ] Expression evaluates first, with effects. -/
| asn :
    ExprStep DataT e loc s v s' →
    step (.run <| .cons ⟨.assign (.some x) e, loc⟩ p, s) (.run <| p.map (.bind _ · x v), s')
/-- [ Sequencing Effects ] -/
| seq :
    ExprStep DataT e loc s _ s' →
    step (.run <| .cons ⟨.assign .none e, loc⟩ p, s) (.run p, s')
/-- [ Loop termination ] -/
| loop_exit {I : Type _} [Iterator I (@Value DataT)] :
    step (.run <| .cons ⟨.loop I _ .none _, _⟩ p, s) (.run p, s)
/-- [ Loop enter body ] -/
| loop_nter {I : Type _} [Iterator I (@Value DataT)] (i : I) :
    step
      (.run <| .cons ⟨.loop I x (.some i) b, loc⟩ p, s)
      (.run <|
          .append (p.map (fun t => t.bind _ x (Iterator.peek i))) <|
          .cons ⟨.loop I x (Iterator.next (@Value DataT) i) b, loc⟩ <|
          p, s)

/- TODO: Write an interpreter and prove it correct. Use a nondeterminism monad. -/
end NML
