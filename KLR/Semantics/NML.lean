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

/-- A physical ChipIndex cannot be free allocated. -/
def ChipIndex.is_physical : KLR.Core.ChipIndex → Prop
| .psumPhysIndex
| .sbufPhysIndex => True
| _ => False

namespace NML

open KLR.Core TensorLib

/-! # NML, Neuron Modeling Language
The language is parameterized by a type of floating point numbers, see `KLR/Semantics/Float.lean`. -/

variable (DataT : Type _)

/-- A pointer to a tensor that carries additional metadata.

NB. No size contstraints on the tensor (like Address). Minimum size can be computed
from shape and layout. -/
structure TensorHandle where
  /-- Memory bank in which the tensor is stored -/
  index : ChipIndex
  /-- Multiaffine equation mapping tensor indices to indices in the address space. -/
  layout : AffineMap
  /-- Logical description of a tensor shape -/
  shape : KLR.Core.Shape
  /-- The affine map must have the same dimensions as -/
  layout_wf : layout.free_strides.length = shape.freeDims.length
  /- Datatype of the tensor's values. TODO: Add a wf predicate to the state interpretation that checks that all tensors are well-typed? -/
  dtype : KLR.Core.Dtype
  /-- (Optional) name of the tensor -/
  name  : Option String

def TensorHandle.get_store? (r : TensorHandle) (m : NeuronMemory DataT) : Option (LocalStore DataT) :=
  ChipMemory.get_store m r.index

/-- NML program stat  -/
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
-- uptr: like a TensorHandle but no metadata. Just a raw pointer to a store that can hold anything.
| uptr     (_ : ChipIndex)

/-- NML expressions. These are terms which reduce to a value and possibly update the state.
There is no control flow inside expressions. -/
inductive Expr
| val           (_ : @Value DataT)
| var           (_ : String)
| load          (_ : AffineMap) (_ : Expr)
| alloc         (m : Memory)
| store         (src : Expr) (_ : AffineMap) (dst : Expr)
| unary_scalar  (_ : Expr) (_ : DataT → DataT)

/-- NML statements.  -/
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
    -- The source tensor must have index in HBM (can be generalized), and be allocated
    tensor.index = ChipIndex.hbmIndex src_index →
    ChipMemory.get_store st'.memory tensor.index = some src_store →
    -- The destination tensor is a fresh tensor in SBUF, with updated state.
    ⟨dst_index, memory''⟩ = ChipMemory.freshSBUFStore st'.memory →
    ExprStep (.load asn e) loc st
      -- Return value: The input tensor, but with its chip index updated to be the fresh tensor.
      -- All other metadata is the same.
      (.ptr {tensor with index := dst_index })
      -- Return state: Update the SBUF state at the fresh index to contain the source store.
      (State.mk <| ChipMemory.set_store memory'' dst_index (some src_store))
/-- [Allocation] Allocate fresh SBUF tensor -/
| sbuf_alloc :
    ⟨dst_index, memory'⟩ = ChipMemory.freshSBUFStore st.memory →
    ExprStep (.alloc Memory.sbuf) loc st (.uptr dst_index) (State.mk memory')


/-
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
-/

theorem expr_step_det : ExprStep DataT e loc s vl sl → ExprStep DataT e loc s vr sr → vl = vr ∧ sl = sr := by
  induction e <;> sorry
/-
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
-/


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
    ExprStep DataT e loc s v s' →
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
