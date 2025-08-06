/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Logic
import KLR.Semantics.ProofRules
import Iris.ProofMode.Tactics
import KLR.Semantics.Tactics

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML Iris.BI

variable {DataT : Type _}

/-- Example relation: Both programs reutrn integers, and the integer of the left program is less
than the integer of the right program. -/

def ΦIsIntLePure (v1 v2 : NML.Value DataT) : Prop := ∃ (z1 z2 : Int), v1 = NML.Value.int z1 ∧ v2 = .int z2 ∧ z1 < z2
def ΦIsIntLe (v1 v2 : NML.Value DataT) : @PROP DataT := iprop(⌜ΦIsIntLePure v1 v2⌝)

/-- Simplest possible example: Two programs in "done" states -/
theorem example0 : ⊢ (@wp DataT ⟨1⟩ (.done (.int 4)) (.done (.int 5)) ΦIsIntLe) := by
  apply Entails.trans ?_ (wpValVal (v1 := .int 4) (v2 := .int 5) (by rfl) (by rfl))
  istart
  simp only [ΦIsIntLe]
  ipure_intro; exists 4; exists 5


set_option linter.deprecated false in
/-- Two "return" programs are related if the values they return are -/
theorem example1 :
  ⊢ @wp DataT ⟨1⟩
      (withNoContext [.ret (.val (.int 4))])
      (withNoContext [.ret (.val (.int 5))])
      ΦIsIntLe := by
  istart
  wp_sync_pure RetPure, RetPure
  wp_sync_val
  simp only [ΦIsIntLe]
  ipure_intro
  exists 4
  exists 5

/-- A proof that both programs
    - Are safe,
    - Are equiterminating,
    - Step to values related by ΦIsIntLePure if they (both) terminate -/
theorem example1_full (σ₁ σ₂ : State DataT) :
  (NMLSemantics DataT).PRel
    ((.run [⟨.ret (.val (.int 4)), fun _ => .none⟩]), σ₁)
    ((.run [⟨.ret (.val (.int 5)), fun _ => .none⟩]), σ₂)
    ΦIsIntLePure := by
  apply wp_adequacy (K := ⟨1⟩)
  istart; iintro H; iclear H; istop
  exact example1

/-! Example 2: Allocation
This is one of the simplest state-transforming ste
Prove that allocation under any heap is safe using a relational proof.
-/

def ex2 : ExecState DataT :=
  (.run [⟨.assign .none (.alloc Memory.sbuf), nolocals _⟩, ⟨.ret <| .val .unit, nolocals _⟩])

theorem example2 (σ : State DataT) : SmallStep.Safe (ex2, σ) := by
  -- It suffices to show that `(ex2, σ) ∼ (ex2, σ) : fun _ _ => True`
  apply SmallStep.Safe_of_PRel (Φf := fun _ _ => True)
  -- Enter the Iris proof
  apply wp_adequacy (K := ⟨1⟩)
  unfold ex2
  sorry


/- ## Example: Desynced stepping of pure expressions -/

def ΦUnitEq (v1 v2 : NML.Value DataT) : @PROP DataT := iprop(⌜v1 = .unit ∧ v2 = .unit⌝)
def e3L : ExecState DataT :=
  withNoContext [
    .assign .none (.val (.int 3)),
    .assign .none (.val (.bool false)),
    .assign .none (.val .unit),
    .assign .none (.val (.int 3)),
    .ret (.val .unit),
  ]

def e3R : ExecState DataT :=
  withNoContext [
    .assign .none (.val .unit),
    .assign .none (.val (.bool false)),
    .ret (.val .unit),
  ]

set_option linter.deprecated false in
theorem e3 : ⊢ @wp DataT ⟨2⟩ e3L e3R ΦUnitEq := by
  simp [e3L, e3R, withNoContext]
  istart
  -- Enter desync mode, do two left pure steps, and one right pure step. Resync.
  -- Note (commented) that a third pure step does not work becase of the ⟨2⟩ bound.
  wp_desync
  dwp_left_pure SeqPure
  dwp_left_pure SeqPure
  -- dwp_left_pure SeqPure
  dwp_right_pure SeqPure
  wp_resync

  -- Do another batch of step
  wp_desync
  dwp_left_pure SeqPure
  dwp_left_pure SeqPure
  dwp_right_pure SeqPure
  wp_resync

  -- And close the proof off like example 1
  wp_sync_pure RetPure, RetPure
  wp_sync_val
  simp [ΦUnitEq]
  exact true_intro

def e4L : ExecState DataT :=
  .run [⟨.assign (.some "x") (.val <| .int 3), nolocals _⟩, ⟨.ret (.var "x"), nolocals _⟩]

def e4R : ExecState DataT :=
  .run [⟨.assign (.some "y") (.val <| .int 3), nolocals _⟩, ⟨.ret (.var "y"), nolocals _⟩]

def ΦInt (R : Int → Int → @PROP DataT) (v1 v2 : NML.Value DataT) : @PROP DataT :=
  iprop(∃ z1 z2, ⌜v1 = .int z1⌝ ∗ ⌜v2 = .int z2⌝ ∗ R z1 z2)
def ΦIntPure (R : Int → Int → Prop) (v1 v2 : NML.Value DataT) : @PROP DataT :=
  ΦInt (fun z1 z2 => (iprop(⌜R z1 z2⌝) : @PROP DataT)) v1 v2

theorem e4 : ⊢ (@wp DataT ⟨1⟩ e4L e4R (ΦIntPure (· = ·))) := by
  unfold e4L e4R
  wp_desync
  dwp_left_pure  AssignPure
  dwp_right_pure AssignPure
  wp_resync
  simp [List.map, NML.Task.bind]
  wp_desync
  dwp_left_pure  (RetPureExpr VarPureE (by rfl))
  dwp_right_pure (RetPureExpr VarPureE (by rfl))
  wp_resync
  wp_desync
  dwp_left_pure  RetPure
  dwp_right_pure RetPure
  wp_resync
  wp_sync_val
  simp [ΦIntPure, ΦInt]
  iexists 3
  iexists 3
  ipure_intro
  simp

theorem e4' : ⊢ (wp (DataT := DataT) ⟨1⟩ e4L e4R (ΦIntPure (· = ·))) := by
  unfold e4L e4R
  wp_desync
  uwp_left  uwpPureL AssignPure
  uwp_right uwpPureR AssignPure
  wp_resync; wp_desync
  uwp_left  uwpPureL <| RetPureExpr VarPureE (by rfl)
  uwp_right uwpPureR <| RetPureExpr VarPureE (by rfl)
  wp_resync; wp_desync
  uwp_left  uwpPureL RetPure
  uwp_right uwpPureR RetPure
  wp_resync; wp_sync_val
  simp [ΦIntPure, ΦInt]
  iexists 3
  iexists 3
  ipure_intro
  simp

def e5L : ExecState DataT :=
  withNoContext [
    .assign .none (.val .unit),
    .ret (.val .unit),
  ]

def e5R : ExecState DataT :=
  withNoContext [
    .assign .none (.val (.bool false)),
    .ret (.val .unit),
  ]

theorem e5 : ⊢ @wp DataT ⟨2⟩ e5L e5R ΦUnitEq := by
  istart
  unfold e5L e5R
  simp [withNoContext]
  wp_desync
  dwp_left_pure  SeqPure
  dwp_right_pure SeqPure
  dwp_left_pure  RetPure
  dwp_right_pure RetPure
  wp_resync
  wp_sync_val
  simp [ΦUnitEq, true_intro]

-- e5 but with uwp
theorem e5' : ⊢ @wp DataT ⟨2⟩ e5L e5R ΦUnitEq := by
  istart
  unfold e5L e5R
  simp [withNoContext]
  wp_desync
  uwp_left  uwpPureL SeqPure
  uwp_left  uwpPureL RetPure
  uwp_right uwpPureR SeqPure
  uwp_right uwpPureR RetPure
  wp_resync
  wp_sync_val
  simp [ΦUnitEq, true_intro]



/-! Example: Loops with .none as next entry are skipped -/

def e6L : ExecState DataT :=
  withNoContext [
    .loop AffineIter "x" .none [],
    .ret (.val .unit),
  ]

def e6R : ExecState DataT :=
  withNoContext [
    .ret (.val .unit),
  ]


theorem e6 : ⊢ @wp DataT ⟨2⟩ e6L e6R ΦUnitEq := by
  simp [withNoContext, e6L, e6R]
  wp_desync
  dwp_left_pure  LoopExitPure
  dwp_left_pure  RetPure
  dwp_right_pure RetPure
  wp_resync
  wp_sync_val
  simp [ΦUnitEq, true_intro]


/-! Example: Loop unrolling
This doesn't demonstrate any interesting unrolling, but it's an example of doing loop unrolling
w/ the proof state. -/

-- The sequence: [2, 4, 6]
def e7Iterator : AffineIter where
  start     := 1
  peek      := 2
  num       := 2
  start_num := 1
  step      := 2

def e7L : ExecState DataT :=
  withNoContext [
    .loop AffineIter "x" (.some e7Iterator) [.assign .none (.val .unit)],
    .ret (.val .unit),
  ]

def e7R : ExecState DataT :=
  withNoContext [
    .assign .none (.val .unit),
    .assign .none (.val .unit),
    .assign .none (.val .unit),
    .ret (.val .unit),
  ]

theorem e7 : ⊢ wp (DataT := DataT) ⟨2⟩ e7L e7R ΦUnitEq := by
  simp [withNoContext, e7L, e7R]
  wp_desync
  dwp_right_pure SeqPure
  dwp_left_pure  LoopNterPure
  dwp_left_pure  SeqPure
  wp_resync
  simp
  wp_desync
  dwp_right_pure SeqPure
  dwp_left_pure  LoopNterPure
  dwp_left_pure  SeqPure
  wp_resync
  simp
  wp_desync
  dwp_right_pure SeqPure
  dwp_left_pure  LoopNterPure
  dwp_left_pure  SeqPure
  wp_resync
  simp
  wp_desync
  dwp_left_pure  LoopExitPure
  dwp_left_pure  RetPure
  dwp_right_pure RetPure
  wp_resync
  wp_sync_val
  simp [ΦUnitEq, true_intro]

theorem e7' : ⊢ wp (DataT := DataT) ⟨2⟩ e7L e7R ΦUnitEq := by
  simp [withNoContext, e7L, e7R]
  wp_desync
  uwp_right uwpPureR SeqPure
  uwp_left  uwpPureL LoopNterPure
  uwp_left  uwpPureL SeqPure
  wp_resync; simp; wp_desync
  uwp_right uwpPureR SeqPure
  uwp_left  uwpPureL LoopNterPure
  uwp_left  uwpPureL SeqPure
  wp_resync; simp; wp_desync
  uwp_right uwpPureR SeqPure
  uwp_left  uwpPureL LoopNterPure
  uwp_left  uwpPureL SeqPure
  wp_resync; simp; wp_desync
  uwp_left  uwpPureL LoopExitPure
  uwp_left  uwpPureL RetPure
  uwp_right uwpPureR RetPure
  wp_resync
  wp_sync_val
  simp [ΦUnitEq, true_intro]

/-- Pure assignments -/

def ΦIntEq (v1 v2 : NML.Value DataT) : @PROP DataT := iprop(⌜∃ z, v1 = .int z ∧ v2 = .int z⌝)

def e8L : ExecState DataT :=
  withNoContext [
    .assign (.some "x") (.val <| .int 3),
    .assign (.some "y") (.var "x"),
    .ret (.var "y"),
  ]

def e8R : ExecState DataT :=
  withNoContext [
    .ret (.val <| .int 3)
  ]

-- TODO: Move
attribute [simp] Locals.bind

theorem e8 : ⊢ wp (DataT := DataT) ⟨5⟩ e8L e8R ΦIntEq := by
  simp [withNoContext, e8L, e8R]
  wp_desync
  dwp_left_pure  AssignPure
  dwp_left_pure  (AssignPureExpr VarPureE (by rfl))
  dwp_left_pure  AssignPure
  dwp_left_pure  (RetPureExpr VarPureE (by rfl))
  dwp_left_pure  RetPure
  dwp_right_pure RetPure
  wp_resync
  wp_sync_val
  simp [ΦIntEq, true_intro]

-- E8 but using the uwp machinery
theorem e8' : ⊢ wp (DataT := DataT) ⟨5⟩ e8L e8R ΦIntEq := by
  simp [withNoContext, e8L, e8R]
  wp_desync
  uwp_left  uwpPureL AssignPure
  uwp_left  LiftEAsn.liftL <| ewpVarL (.int 3)
  uwp_left  uwpPureL AssignPure
  uwp_left  LiftERet.liftL <| ewpVarL (.int 3)
  uwp_left  uwpPureL RetPure
  uwp_right uwpPureR RetPure
  wp_resync
  wp_sync_val
  simp [ΦIntEq, true_intro]



/-! Example 9: Partiality -/

structure LoopIter where

-- TODO: I don't actually want to use the TensorLib iterator for this.
-- "size" is not defined and "reset" will cause annoyances with Lob induction.
instance instLoopIterator {DataT : Type _} : TensorLib.Iterator LoopIter (NML.Value DataT) where
  next  := fun i => .some i
  peek  := fun _ => .unit
  size  := fun _ => 0
  reset := fun _ => ⟨⟩

def e9L : ExecState DataT :=
  withNoContext [
    .loop LoopIter "x" (.some ⟨⟩) [.assign .none (.val .unit)],
    -- No return, stuck
  ]

def e9R : ExecState DataT :=
  withNoContext [
    .loop LoopIter "y" (.some ⟨⟩) [.assign .none (.val .unit)],
    .ret (.val .unit)
  ]


theorem e9 : ⊢ wp (DataT := DataT) ⟨5⟩ e9L e9R ΦIntEq := by
  simp [withNoContext, e9L, e9R]
  istart
  have Z := @wp_gen_loc DataT ⟨5⟩
                (Stmt.loop LoopIter "x" (some { }) [NML.Stmt.assign none (Expr.val Value.unit)])
                []
                (Stmt.loop LoopIter "y" (some { }) [NML.Stmt.assign none (Expr.val Value.unit)])
                [{ stmt := NML.Stmt.ret (Expr.val Value.unit), env := nolocals DataT }]
                ΦIntEq
                (nolocals DataT)
                (nolocals DataT)
                (fun _ _ => True)
  refine include_sep Z ?_; clear Z
  iintro ⟨H, Hemp⟩
  iclear Hemp
  iapply H
  · iintro locₗ locᵣ Hemp; iclear Hemp
    -- Here is where I'd apply the Loeb lemma
    -- Also: need to be allowed to eliminate laters in the hypothesis
    sorry
  · exact fun n x a a => a

/-! Example: Pure loop fusion

NB. This is hard to extract as a general pattern right now because the wp
doesn't satisfy a bind rule. MARKUSDE: Think more on swp idea. -/

structure ProgressIter (T : Type _) where
  state   : Nat
  initial : Nat
  interp  : Nat → T

instance : TensorLib.Iterator (ProgressIter T) T where
  next  i := match i.state with | 0 => none | .succ n' => some { i with state := n' }
  peek  i := i.interp i.state
  size  i := i.initial
  reset i := { i with state := i.initial }

-- To make this example interesting:
-- -> A shape [n] tensor v in SBUF
-- -> A function to change a single element of the tensor
-- -> Fine-grained ownership notation ⟨ℓ₁, i⟩ ↦ x
-- -> Ownership equation (ℓₗ [S]⇉ₗ v) ⊢ ([∗] i, ⟨ℓₗ, i⟩ ↦ v[i])


/- Reading and writing a point -/

-- dwp read
-- Example: Given left points to, updates the left points to, reads and returns it, right is a value, prove equal

-- dwpReadpRetL

def e10L (ℓ : ChipIndex) (x : Nat × Nat) (d₀ : DataT): ExecState DataT :=
  withNoContext [
    .set_point (.val <| .uptr ℓ) (.val <| .iptr x) (.val <| .data d₀),
    .ret (.read_point (.val <| .uptr ℓ) (.val <| .iptr x)),
  ]

def e10R (d₀ : DataT) : ExecState DataT :=
  withNoContext [
    .ret (.val <| .data d₀)
  ]

def ΦEq (v1 v2 : NML.Value DataT) : @PROP DataT := iprop(⌜v1 = v2⌝)

theorem e10 (ℓ : ChipIndex) (x : Nat × Nat) (mv : Option DataT) (d₀ : DataT) :
    (⟨ℓ, x⟩ ↦ₗ mv) ⊢ wp (DataT := DataT) ⟨5⟩ (e10L ℓ x d₀) (e10R d₀) ΦEq := by
  iintro Hfrag
  wp_desync
  simp [withNoContext, e10L, e10R]
  refine .trans ?_ (dwpSetpL' (mv := mv))
  iintro Hfrag'
  isplit l [Hfrag']; iexact Hfrag'
  iintro Hfrag'
  istop; refine .trans ?_ (dwpReadpRetL' (v := d₀)); istart
  iintro H
  isplit l [H]; iexact H
  iintro - -- The frag coupling is not used
  uwp_left  uwpPureL RetPure
  uwp_right uwpPureR RetPure
  wp_resync
  wp_sync_val
  simp [ΦEq, true_intro]

