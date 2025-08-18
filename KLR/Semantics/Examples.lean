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

set_option grind.warning false
variable {DataT : Type _} [NMLEnv DataT]
attribute [simp] Locals.bind


@[simp] def ΦInt (Φ : Int → Int → Prop) (v1 v2 : Value DataT) : Prop :=
  ∃ z1 z2, v1 = .int z1 ∧ v2 = .int z2 ∧ Φ z1 z2
@[simp] def ΦPure (Φ : Value DataT → Value DataT → Prop) : Value DataT → Value DataT → @PROP DataT :=
  (iprop(⌜Φ · ·⌝))
@[simp] def ΦTriv (_ _ : Value DataT) : Prop := True

namespace example0
/-! Example: Done states are related-/

abbrev K : Nat := 1
@[simp] def sL : ProgState DataT := ⟨.done <| .int 4, []⟩
@[simp] def sR : ProgState DataT := ⟨.done <| .int 5, []⟩

theorem example0 : ⊢ wp (DataT := DataT) K sL sR (ΦPure <| ΦInt (· < ·)) := by
  simp [sL, sR]
  wp_sync_val
  unfold ΦPure ΦInt
  ipure_intro
  grind

/-- Applying the NML Adequacy theorem to example0 -/
example (σ₁ σ₂ : State DataT) : SmallStep.PRel (Prog := NML.ProgState DataT) (sL, σ₁) (sR, σ₂) (ΦInt (· < ·)) := by
  apply wp_adequacy (K := 1)
  refine .trans ?_ example0
  exact true_intro.trans true_emp.mp

end example0

namespace example1
/-! Example: Desync, step left and right, and return -/

@[simp] def sL : ProgState DataT := ⟨.run ⟨[.ret <| .val <| .int 4], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[.ret <| .val <| .int 4], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 1 sL sR (ΦPure <| ΦInt (· = ·)) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦInt
  ipure_intro
  grind

end example1

namespace example2
/-! Example: Proving safety of a program -/

@[simp] def s : ProgState DataT := ⟨.run ⟨[.ret <| .val <| .int 4], .emp⟩, []⟩

theorem example2 : ⊢ wp (DataT := DataT) 2 s s (ΦPure ΦTriv) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦTriv
  ipure_intro
  grind

example (σ : State DataT) : SmallStep.Safe (Prog := NML.ProgState DataT) (s, σ) := by
  apply SmallStep.Safe_of_PRel (Φf := ΦTriv)
  apply wp_adequacy (K := 2)
  refine .trans ?_ example2
  exact true_intro.trans true_emp.mp

end example2

namespace example3
/-! Example: Step value assignment -/

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .assign (.some "x") (.val .unit),
    .ret <| (.val .unit)
  ], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val .unit)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 2 sL sR (ΦPure ΦTriv) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .assign trivial
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦTriv
  ipure_intro
  grind

end example3

namespace example4
/-! Example: Step sequencing assignment -/

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .assign .none (.val .unit),
    .ret <| (.val .unit)
  ], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val .unit)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 2 sL sR (ΦPure ΦTriv) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .seq trivial
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦTriv
  ipure_intro
  grind

end example4

namespace example5
/-! Example: Step empty assignment -/

variable (n : Nat) (i : IteratorS)

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .mkiter n i,
    .ret <| (.val .unit)
  ], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val .unit)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 2 (sL n i) sR (ΦPure ΦTriv) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .mkiter trivial
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦTriv
  ipure_intro
  grind

end example5


-- namespace example6
-- /-! Example: Step empty assignment -/
--
-- variable (c' : LocalContext DataT)
--
-- @[simp] def sL : ProgState DataT := ⟨.run ⟨[
--     .frame [] c',
--     .ret <| (.val .unit)
--   ], .emp⟩, []⟩
-- @[simp] def sR : ExecState DataT := .run [
--     .ret <| (.val .unit)
--   ] .emp
--
-- example : ⊢ wp (DataT := DataT) 2 (sL c') sR (ΦPure ΦTriv) := by
--   istart
--   wp_desync
--   uwp_left  SPure.uwpL .frameEmp trivial
--   uwp_left  SPure.uwpL .ret trivial
--   uwp_right SPure.uwpR .ret trivial
--   wp_resync
--   wp_sync_val
--   unfold ΦPure ΦTriv
--   ipure_intro
--   grind
--
-- end example6

namespace example7
/-! Example: Loop exit -/

variable (n : Nat) (i : Iterator DataT) (b : List (Stmt DataT))
variable (Hloop : PLoopExit (LocalContext.bindi .emp n i) n)

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .loop "x" (.val <| .iref n) b,
    .ret <| (.val .unit)
  ], (LocalContext.bindi .emp n i)⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val .unit)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 2 (sL n i b) sR (ΦPure ΦTriv) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .loopExit Hloop
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦTriv
  ipure_intro
  grind

end example7

namespace example8
/-! Example: Lifting pure expr steps -/

variable (f : NML.Dunop DataT) (d₀ d₁ : DataT) (Hf : NMLEnv.evalDunop f d₀ = d₁)

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .ret <| (.dunop (.val <| .data d₀) f)
  ], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val <| .data d₁)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 2 (sL f d₀) (sR d₁) (ΦPure (· = ·)) := by
  istart
  wp_desync
  uwp_left EPLift.uwpL EPLift.ret_arg <| EPure.ewpL <| EPure.dunop
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure
  ipure_intro
  grind

end example8


namespace example9
/-! Example: Variable assignment -/

variable (d₀ : DataT)

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .assign (some "x") (.val <| .data d₀),
    .assign (some "y") (.var "x"),
    .ret <| (.var "y")
  ], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val <| .data d₀)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 5 (sL d₀) (sR d₀) (ΦPure (· = ·)) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .assign trivial
  uwp_left  EPLift.uwpL EPLift.assign_arg <| EPure.ewpL <| EPure.var (v := .data d₀)
  uwp_left  SPure.uwpL .assign trivial
  uwp_left  EPLift.uwpL EPLift.ret_arg <| EPure.ewpL <| EPure.var (v := .data d₀)
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure
  ipure_intro
  grind

end example9

namespace example10
/-! Example: Variable assignment -/

variable (d₀ : DataT)

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .assign (some "x") (.val <| .data d₀),
    .assign (some "y") (.var "x"),
    .ret <| (.var "y")
  ], .emp⟩, []⟩
@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .ret <| (.val <| .data d₀)
  ], .emp⟩, []⟩

example : ⊢ wp (DataT := DataT) 5 (sL d₀) (sR d₀) (ΦPure (· = ·)) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .assign trivial
  uwp_left  EPLift.uwpL EPLift.assign_arg <| EPure.ewpL <| EPure.var (v := .data d₀)
  uwp_left  SPure.uwpL .assign trivial
  uwp_left  EPLift.uwpL EPLift.ret_arg <| EPure.ewpL <| EPure.var (v := .data d₀)
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure
  ipure_intro
  grind

end example10


namespace example11
/-! Example: Safety of nonphysical allocation -/

@[simp] def s : ProgState DataT := ⟨.run ⟨[
    .assign (some "ℓ") (.alloc .sbuf),
    .ret <| (.var "ℓ")
  ], .emp⟩, []⟩

/- Best we can get with our dwpL/R proof rules: there exists a chip -/
@[simp] def ΦBothLoc (v1 v2 : Value DataT) : Prop :=
  ∃ cl cr, v1 = .uptr cl ∧ v2 = .uptr cr

example : ⊢ wp (DataT := DataT) 5 s s (ΦPure ΦBothLoc) := by
  istart
  wp_desync
  dwp_left dwpAllocL (Hx := by simp) -- FIXME: Why does this not go automatically?
  iintro ℓₗ Hℓ₁
  dwp_right dwpAllocR
  iintro Hℓₗ ℓᵣ Hℓᵣ
  wp_resync

  wp_desync
  -- TODO: Make the value be infered by unification
  uwp_left  EPLift.uwpL EPLift.ret_arg <| EPure.ewpL <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓₗ)
  -- TODO: Automatically reintroduce the entire context, or better yet, use iapply instead of .trans
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.ret_arg <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left  SPure.uwpL .ret trivial
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right SPure.uwpR .ret trivial
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  wp_sync_val
  iintro -
  unfold ΦPure
  ipure_intro
  exists .sbufUnboundedIndex ℓₗ
  exists .sbufUnboundedIndex ℓᵣ

end example11

namespace example12
/-! Example: Loop stuff -/

abbrev K : Nat := 5


end example12




-- Big list of example ideas:
-- dwpSetpR/L to uwp to test impure steps
-- Lift impure expr steps (reading)
-- Done states adequacy with locals
-- Done states with different values
-- Returns
-- Returns with different values
-- (All) Pure steps
-- Safety
-- Rule to Step inside frame
-- Loop continue

-- Open questions:
-- Composition (seq rule for frame steps)
-- Monotonicity of K
-- Improved surface syntax
-- Better timeout on the tactics
-- ret_assert and adequacy







/-


/-! Example 2: Allocation
This is one of the simplest state-transforming ste
Prove that allocation under any heap is safe using a relational proof.
-/

def ex2 : ExecState DataT :=
  (.run [⟨.assign .none (.alloc Memory.sbuf), Locals.Emp _⟩, ⟨.ret <| .val .unit, Locals.Emp _⟩])

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
  .run [⟨.assign (.some "x") (.val <| .int 3), Locals.Emp _⟩, ⟨.ret (.var "x"), Locals.Emp _⟩]

def e4R : ExecState DataT :=
  .run [⟨.assign (.some "y") (.val <| .int 3), Locals.Emp _⟩, ⟨.ret (.var "y"), Locals.Emp _⟩]

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
  sorry
  -- dwp_left_pure  SeqPure
  -- wp_resync
  -- simp
  -- wp_desync
  -- dwp_right_pure SeqPure
  -- dwp_left_pure  LoopNterPure
  -- dwp_left_pure  SeqPure
  -- wp_resync
  -- simp
  -- wp_desync
  -- dwp_right_pure SeqPure
  -- dwp_left_pure  LoopNterPure
  -- dwp_left_pure  SeqPure
  -- wp_resync
  -- simp
  -- wp_desync
  -- dwp_left_pure  LoopExitPure
  -- dwp_left_pure  RetPure
  -- dwp_right_pure RetPure
  -- wp_resync
  -- wp_sync_val
  -- simp [ΦUnitEq, true_intro]

theorem e7' : ⊢ wp (DataT := DataT) ⟨2⟩ e7L e7R ΦUnitEq := by
  simp [withNoContext, e7L, e7R]
  wp_desync
  uwp_right uwpPureR SeqPure
  uwp_left  uwpPureL LoopNterPure
  sorry
  -- uwp_left  uwpPureL SeqPure
  -- wp_resync; simp; wp_desync
  -- uwp_right uwpPureR SeqPure
  -- uwp_left  uwpPureL LoopNterPure
  -- uwp_left  uwpPureL SeqPure
  -- wp_resync; simp; wp_desync
  -- uwp_right uwpPureR SeqPure
  -- uwp_left  uwpPureL LoopNterPure
  -- uwp_left  uwpPureL SeqPure
  -- wp_resync; simp; wp_desync
  -- uwp_left  uwpPureL LoopExitPure
  -- uwp_left  uwpPureL RetPure
  -- uwp_right uwpPureR RetPure
  -- wp_resync
  -- wp_sync_val
  -- simp [ΦUnitEq, true_intro]

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
                [{ stmt := NML.Stmt.ret (Expr.val Value.unit), env := Locals.Emp DataT }]
                ΦIntEq
                (Locals.Emp DataT)
                (Locals.Emp DataT)
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
    .setp (.val <| .uptr ℓ) (.val <| .iptr x) (.val <| .data d₀),
    .ret (.readp (.val <| .uptr ℓ) (.val <| .iptr x)),
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
  -- TODO: Turn dwpSetPL' into a uwp instance
  iintro H
  refine .trans ?_ (dwpSetpL' (mv := mv))
  iintro Hfrag'
  isplit l [Hfrag']; iexact Hfrag'
  iintro Hfrag'
  -- TODO: readp should have a uwp
  istop; refine .trans ?_ (dwpReadpRetL' (v := d₀)); istart
  iintro H
  isplit l [H]; iexact H
  iintro - -- The frag part is not used
  uwp_left  uwpPureL RetPure
  uwp_right uwpPureR RetPure
  wp_resync
  wp_sync_val
  simp [ΦEq, true_intro]

-- TODO: e10 but step the expressions using the ewp machinery

section e11

variable (body : List Stmt) (binder : String)

-- Indexed precondition / postcondition. Eliminate bad Local contexts (out of range index
-- or bad local contexts) using False as a precondition
variable (PRE POST : Locals DataT → Nat → PROP DataT)

-- I can define this semantically.
-- wp P (fun _ => wp Q Φ) -∗ wp (P <> Q) Φ
-- when the scope of P ends before Q

-- Define what it means for a subprogram to respect scope

-- Then the next problem: what about relations?
-- When the loop heads line up syntactically, it is fine. That can be the first relational
-- rule I prove. When the looping structures are different I want to do this proof step using
-- variables, basically.

-- So we assign ghost variables to each iterator in each program, an (indexed) bijection between their values,
-- and then we have a rule which says it suffices to









end e11
-/
