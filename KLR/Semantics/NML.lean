/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.Lib
import KLR.Semantics.Memory
import KLR.Semantics.SmallStep
import TensorLib.Iterator

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

/-! # NML, Neuron Modeling Language
The language is parameterized by a type of floating point numbers, see `KLR/Semantics/Float.lean`. -/

variable (DataT : Type _)

/-- A pointer to a tensor that carries additional metadata. -/
structure TensorHandle extends KLR.Core.TensorName where
  /-- The memory bank where the tensor is being stored in our memory model -/
  index : KLR.Core.DualMemoryStoreIndex
  /-- Is the tensor physical (UInt8) or nonphysical (DataT)? -/
  is_physical : Bool
  /-- Multiaffine equation mapping tensor indices to Address indices. -/
  layout : AffineMap

/-- Get the LocalStore that a TensorHandle is pointing to. -/
def TensorHandle.get_store? (r : TensorHandle) (m : NeuronMemory DataT) : Option (LocalStore (UCell UInt8 DataT)) :=
  match r.address.memory, r.index with
  | .hbm, .in_bounded => .none
  | .hbm, .in_unbounded i => m.hbm[i]?
  | .sbuf, .in_bounded => .some m.sbuf.bounded.toLocalStore
  | .sbuf, .in_unbounded i => m.sbuf.unbounded[i]?
  | .pmem, _ => .none
  | .reg, _ => .none

def TensorHandle.hbm_index? (r : TensorHandle) : Option Nat :=
  match r.index with
  | .in_bounded => .none
  | .in_unbounded i => .some i

/-- Update a given store in the NeuronMemory. Returns None if updating a store that is out of bounds. -/
def TensorHandle.upd_store? (r : TensorHandle) (m : NeuronMemory DataT)
      (L : LocalStore (UCell UInt8 DataT) → LocalStore (UCell UInt8 DataT)) :
    Option (NeuronMemory DataT) :=
  match r.address.memory, r.index with
  | .hbm, .in_bounded => .none
  | .hbm, .in_unbounded i => do
      let _ ← m.hbm[i]?
      return { m with hbm := m.hbm.set i L }
  | .sbuf, .in_bounded =>
      .some { m with sbuf.bounded.toLocalStore := L m.sbuf.bounded.toLocalStore }
  | .sbuf, .in_unbounded i => do
      let _ ← m.sbuf.unbounded[i]?
      return { m with sbuf.unbounded := m.sbuf.unbounded.set i L }
  -- pmem and reg are currently not supported by NML
  | .pmem, _ => .none
  | .reg, _ => .none

/-- NML state. -/
structure State where
  memory : KLR.Core.NeuronMemory DataT

/-- NML values. These are fully-reduced expressions. -/
inductive Value
| unit
| bool     (_ : Bool)
| data     (_ : DataT)
| int      (_ : Int)
| linfunc  (_ : AffineMap)
| ptr      (_ : TensorHandle)

/-- NML expressions. These are terms which reduce to a value and possibly update the state.
There is no control flow inside expressions. -/
inductive Expr
| val           (_ : @Value DataT)
| var           (_ : String)
| load          (_ : AffineMap) (_ : Expr)
| store         (src : Expr) (_ : AffineMap) (dst : Expr)
| unary_scalar  (_ : Expr) (_ : DataT → DataT)

/-- NML statements. Control flow lives here. -/
inductive Stmt where
| ret          (_ : @Expr DataT)
| assign       (_ : Option String) (_ : @Expr DataT)
| loop         (I : Type _) [Iterator I (@Value DataT)] (_ : String) (_ : Option I) (body : Stmt) (body : List Stmt)
| edit_state   (_ : @State DataT → @State DataT)
| ret_assert   (_ : @Expr DataT) (_ : @State DataT → Prop)

def Expr.is_value? : Expr DataT → Prop | .val _ => True | _ => False

abbrev Expr.pure? : @Expr DataT → Prop
| .val _ | .var _ => True
| _ => False

structure PureExpr where
  expr : @Expr DataT
  pure : Expr.pure? DataT expr

def Value.as_handle? : @Value DataT → Option TensorHandle | .ptr t => .some t | _ => .none

def Locals := String → Option (@Value DataT)

def Locals.bind (s : @Locals DataT) (x : String) (v : @Value DataT) : @Locals DataT :=
  fun x' => if x = x' then .some v else s x'

/-- Task: a Stmt that needs to be executed in particular local context. -/
structure Task where
  stmt : Stmt DataT
  env : Locals DataT

/-- Bind a new variable in a Task-/
def Task.bind (T : Task DataT) (x : String) (v : Value DataT) : Task DataT :=
  { T with env := T.env.bind DataT x v }

/-- A NML Program during execution. Namely, one of
- A list of tasks to complete,
- A completed execution, with its return value. -/
inductive ExecState where
| run   (_ : List (Task DataT))
| done  (_ : Value DataT)

/-- Expressions semantics -/
inductive ExprStep : @Expr DataT → @Locals DataT → @State DataT → @Value DataT → @State DataT → Type _ where
/-- [value] -/
| value :
    v' = v →
    ExprStep (.val v') loc st v st
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
-- -- /-- [unary scalar] Idealized pure function application to a tensor, in-place.
-- -- Returns the address of the tensor. -/
-- | unary_scalar :
--     ExprStep e l0 s0 (.ptr tensor) s1 →
--     tensor.upd_store? DataT s1.memory (lift_encoding_to_store DataT f) = .some s2 →
--     ExprStep (.unary_scalar e f) l0 s0 (.ptr tensor) { s1 with memory := s2 }


theorem expr_step_det : ExprStep DataT e loc s vl sl → ExprStep DataT e loc s vr sr → vl = vr ∧ sl = sr := by
  induction e
  · rintro ⟨rfl⟩ ⟨rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨H1⟩ ⟨H2⟩
    obtain ⟨rfl⟩ : some vl = some vr := by rename_i H1 H2; exact H1 ▸ H2
    exact ⟨rfl, rfl⟩
  · rename_i _ e IH
    rintro H1 H2
    apply IH <;> clear IH
    · sorry
    · sorry
  · sorry
  · sorry


inductive step : ExecState DataT × State DataT → ExecState DataT × State DataT → Prop where
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
    step (.run <| .cons ⟨.loop I _ .none _ _, _⟩ p, s) (.run p, s)
/-- [ Loop enter body ] -/
| loop_nter {I : Type _} [Iterator I (@Value DataT)] (i : I) :
    step
      (.run <| .cons ⟨.loop I x (.some i) b _, loc⟩ p, s)
      (.run <|
          .append (p.map (fun t => t.bind _ x (Iterator.peek i))) <|
          .cons ⟨.loop I x (Iterator.next (@Value DataT) i) b _, loc⟩ <|
          p, s)
/-- [ghost edit state] Apply a function to the current state. This is ghost code.
This is erasable when f is a no-op. -/
| edit_state {f : State DataT → State DataT} :
    step (.run <| .cons ⟨.edit_state f, e⟩ p, s) (.run <| p, f s)
/-- [ghost return] Returns, but gets stuck if `P` does not hold of the current state.
 is erasable when `P` is always true. -/
| ret_assert {P : State DataT → Prop} :
    P s →
    step (.run <| .cons ⟨.ret_assert e P, loc⟩ ps, s) (.done v, s')

@[simp] def to_val : ExecState DataT → Option (Value DataT)
| .done v => .some v
| _ => .none

def NMLSemantics : SmallStep where
  Prog := ExecState DataT
  State := State DataT
  Val := Value DataT
  Step := step DataT
  toVal := to_val DataT
  toVal_isSome_isStuck{c c'} := by
    rintro _ _ H
    cases c
    · cases H
    cases H
    rintro H <;> cases H

instance : Det (NMLSemantics DataT) where
  step_det {c c'} := by sorry
    /-
    rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> try rfl
    · rename_i He1 _ _ He2
      rcases expr_step_det _ He1 He2 with ⟨H1, H2⟩
      subst H1; subst H2; rfl
    · sorry
    · congr
      rename_i He1 _ _ He2
      rcases expr_step_det _ He1 He2 with ⟨H1, H2⟩
      exact H2.symm
    · sorry
    · congr
      rename_i He1 _ _ He2
      rcases expr_step_det _ He1 He2 with ⟨H1, H2⟩
      exact H2.symm
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    -/
  step_progress := sorry

end NML

/-
def lift_encoding_to_store (f : DataT → DataT) : LocalStore UInt8 → LocalStore UInt8 :=
  sorry
-/
