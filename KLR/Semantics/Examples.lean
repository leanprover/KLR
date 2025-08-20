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

/- Not a real loop unrolling example but just one to test some tactics -/

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .mkiter 1 (.affineRange 1 2 4),
    .loop "y" (.val <| .iref 1) [
      .assign .none (.val .unit)
     ],
    .ret <| .val <| .unit
  ], .emp⟩, []⟩

@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .assign .none <| .val .unit,
    .assign .none <| .val .unit,
    .assign .none <| .val .unit,
    .assign .none <| .val .unit,
    .assign .none <| .val .unit,
    .ret <| .val <| .unit,
  ], .emp⟩, []⟩



attribute [local simp] LocalContext.emp Iterators.emp Iterators.bind Iterator.peek
  TensorLib.Iterator.peek IteratorS.toIterator Option.bind Iterator.advance
  Iterators.bind_bind

example : ⊢ wp (DataT := DataT) 5 sL sR (ΦPure (· = ·)) := by
  unfold sL
  unfold sR
  istart
  wp_desync
  uwp_left  SPure.uwpL .mkiter trivial
  uwp_left  SPure.uwpL (.loopContinue (v := .int 1)) (by simp)
  uwp_left  SPure.uwpL .seq trivial
  uwp_left  SPure.uwpL .frameExit trivial
  uwp_right SPure.uwpR .seq trivial
  wp_resync
  wp_desync
  uwp_left  SPure.uwpL (.loopContinue (v := .int 3)) (by simp)
  uwp_left  SPure.uwpL .seq trivial
  uwp_left  SPure.uwpL .frameExit trivial
  uwp_right SPure.uwpR .seq trivial
  wp_resync
  wp_desync
  uwp_left  SPure.uwpL (.loopContinue (v := .int 5)) (by simp)
  uwp_left  SPure.uwpL .seq trivial
  uwp_left  SPure.uwpL .frameExit trivial
  uwp_right SPure.uwpR .seq trivial
  wp_resync
  wp_desync
  uwp_left  SPure.uwpL (.loopContinue (v := .int 7)) (by simp)
  uwp_left  SPure.uwpL .seq trivial
  uwp_left  SPure.uwpL .frameExit trivial
  uwp_right SPure.uwpR .seq trivial
  wp_resync
  wp_desync
  uwp_left  SPure.uwpL (.loopContinue (v := .int 9)) (by simp)
  uwp_left  SPure.uwpL .seq trivial
  uwp_left  SPure.uwpL .frameExit trivial
  uwp_right SPure.uwpR .seq trivial
  wp_resync
  wp_desync
  uwp_left  SPure.uwpL .loopExit (by simp)
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure
  ipure_intro
  grind

end example12


-- Tensor scalar: nisa.tensor_scalar


namespace example13

variable (d₀ : DataT)

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .assign (some "ℓ") (.alloc .sbuf),
    .mkiter 1 (.affineRange 1 2 3),
    .tsdunop (.var "ℓ") .cst (.val <| .data d₀),
    .loop "z" (.val <| .iref 1) [
      .tsdunop (.var "ℓ") .add (.var "z"),
    ],
    .ret <| (.deref_store (.var "ℓ")),
  ], .emp⟩, []⟩

@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .assign (some "ℓ") (.alloc .sbuf),
    .tsdunop (.var "ℓ") .cst (.val <| .data d₀),
    .tsdunop (.var "ℓ") .add (.val <| .int 1),
    .tsdunop (.var "ℓ") .add (.val <| .int 3),
    .tsdunop (.var "ℓ") .add (.val <| .int 5),
    .tsdunop (.var "ℓ") .add (.val <| .int 7),
    .ret <| (.deref_store (.var "ℓ")),
  ], .emp⟩, []⟩

-- TSDunop cst no frame L
theorem dwp_step_1 (H : 0 < Lx) :
      ℓₗ [S]⇉ₗ∅ ∗ ((ℓₗ [S]⇉ₗ (TSDunop.app_cst d₀)) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx ⟨.run ⟨pL, ctx⟩, []⟩ pR Φ )
    ⊢ dwp Lm Rm Lx Rx ⟨.run ⟨.tsdunop (.val <| .uptr <| .sbufUnboundedIndex ℓₗ) .cst (.val <| .data d₀) :: pL, ctx⟩, []⟩ pR Φ := sorry

-- TSDunop cst no frame R
theorem dwp_step_2 (H : 0 < Rx) :
      ℓᵣ [S]⇉ᵣ∅ ∗ ((ℓᵣ [S]⇉ᵣ (TSDunop.app_cst d₀)) -∗ dwp Lm (Rm - 1) Lx (Rx - 1) pL ⟨.run ⟨pR, ctx⟩, []⟩ Φ )
    ⊢ dwp Lm Rm Lx Rx pL ⟨.run ⟨.tsdunop (.val <| .uptr <| .sbufUnboundedIndex ℓᵣ) .cst (.val <| .data d₀) :: pR, ctx⟩, []⟩ Φ := sorry

-- TSDunop add no frame
theorem dwp_step_3 {s : LocalStore DataT} (H : 0 < Rx) :
      (ℓᵣ [S]⇉ᵣ s) ∗ ((ℓᵣ [S]⇉ᵣ (TSDunop.app_addZ s z)) -∗ dwp Lm (Rm - 1) Lx (Rx - 1)  pL ⟨.run ⟨pR, ctx⟩, []⟩ Φ )
    ⊢ dwp Lm Rm Lx Rx pL ⟨.run ⟨.tsdunop (.val <| .uptr <| .sbufUnboundedIndex ℓᵣ) .add (.val <| .int z) :: pR, ctx⟩, []⟩ Φ := sorry

-- TSDunop add no frame
theorem dwp_step_4 (H : LocalContext.getv ctx "ℓ" = some v) (H : 1 < Lx) :
    (dwp (Lm - 1) Rm (Lx - 1) Rx (DataT := DataT) ⟨.run (.tsdunop (.val v) .add (.var "z") :: pL, ctx), F⟩ pR Φ)
  ⊢ (dwp Lm Rm Lx Rx (DataT := DataT) ⟨.run (.tsdunop (.var "ℓ") .add (.var "z") :: pL, ctx), F⟩ pR Φ) := sorry

-- TSDunop add no frame
theorem dwp_step_5 (H : LocalContext.getv ctx "z" = some v) (H : 0 < Lx) :
    (dwp (Lm - 1) Rm (Lx - 1) Rx (DataT := DataT) ⟨.run (.tsdunop (.val (.uptr <| .sbufUnboundedIndex ℓₗ)) .add (.val v) :: pL, ctx), F⟩ pR Φ)
  ⊢ (dwp Lm Rm Lx Rx (DataT := DataT) ⟨.run (.tsdunop (.val (.uptr <| .sbufUnboundedIndex ℓₗ)) .add (.var "z") :: pL, ctx), F⟩ pR Φ) := sorry

theorem dwp_step_6 {s : LocalStore DataT} (Hx : 0 < Lx):
    (ℓₗ [S]⇉ₗ s) ∗ ((ℓₗ [S]⇉ₗ (TSDunop.app_addZ s z)) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (DataT := DataT) ⟨.run (pL, ctx), F⟩ pR Φ)
  ⊢ (dwp Lm Rm Lx Rx (DataT := DataT) ⟨.run (.tsdunop (.val (.uptr <| .sbufUnboundedIndex ℓₗ)) .add (.val <| .int z) :: pL, ctx), F⟩ pR Φ) := sorry


attribute [local simp] LocalContext.emp Iterators.emp Iterators.bind Iterator.peek
  TensorLib.Iterator.peek IteratorS.toIterator Option.bind Iterator.advance


example : ⊢ wp (DataT := DataT) 7 (sL d₀) (sR d₀) (ΦPure (· = ·)) := by
  istart
  -- First desync block:
  -- - Step the left and right sides to allocate the variable ℓ
  -- - Step the left side to allocate the iterator
  -- - Step the left and right sides to apply the zeroing dunop
  wp_desync
  dwp_left dwpAllocL
  iintro ℓₗ Hℓ₁
  dwp_right dwpAllocR
  iintro Hℓₗ ℓᵣ Hℓᵣ
  uwp_left  SPure.uwpL .mkiter trivial
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left  EPLift.uwpL EPLift.tsdunop_loc <| EPure.ewpL <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓₗ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩

  refine .trans ?_ (dwp_step_1 d₀ (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l [Hℓₗ]
  · iexact Hℓₗ
  iintro Hℓₗ

  refine .trans ?_ (dwp_step_2 d₀ (by omega))
  iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l [Hℓᵣ]
  · iexact Hℓᵣ
  iintro Hℓₗ
  wp_resync


  -- Loop desync blocks:
  -- Left side:
  --   - Open the loop body
  --   - Step the var from "ℓ" to the pointer
  --   - Step the value from "z" to the integer
  --   - Step the tsdunop statement
  --   - Close the loop body
  -- Right side
  --   - Step the var from "ℓ" to the pointer
  --   - Step the tsdunop statement
  wp_desync
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_3 (s := TSDunop.app_cst d₀) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l [Hℓᵣ]
  · iexact Hℓᵣ
  iintro Hℓᵣ
  uwp_left  SPure.uwpL (.loopContinue (v := .int 1)) (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_4 (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_5 (v := .int 1) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_6 (s := TSDunop.app_cst d₀) (ℓₗ := ℓₗ) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l [Hℓₗ]
  · iexact Hℓₗ
  iintro Hℓₗ
  uwp_left  SPure.uwpL .frameEmp (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- Do the block again
  wp_desync
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_3 (s := TSDunop.app_addZ (TSDunop.app_cst d₀) 1) (by omega))
  iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l [Hℓᵣ]
  · iexact Hℓᵣ
  iintro Hℓᵣ
  uwp_left  SPure.uwpL (.loopContinue (v := .int 3)) (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_4 (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_5 (v := .int 3) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_6 (s := TSDunop.app_addZ (TSDunop.app_cst d₀) 1) (ℓₗ := ℓₗ) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l [Hℓₗ]
  · iexact Hℓₗ
  iintro Hℓₗ
  uwp_left  SPure.uwpL .frameEmp (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- Do the block again
  wp_desync
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_3 (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst d₀) 1) 3) (by omega))
  iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l [Hℓᵣ]
  · iexact Hℓᵣ
  iintro Hℓᵣ
  uwp_left  SPure.uwpL (.loopContinue (v := .int 5)) (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_4 (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_5 (v := .int 5) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_6 (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst d₀) 1) 3) (ℓₗ := ℓₗ) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l [Hℓₗ]
  · iexact Hℓₗ
  iintro Hℓₗ
  uwp_left  SPure.uwpL .frameEmp (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- Do the block again
  wp_desync
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_3 (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst d₀) 1) 3) 5) (by omega))
  iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l [Hℓᵣ]
  · iexact Hℓᵣ
  iintro Hℓᵣ
  uwp_left  SPure.uwpL (.loopContinue (v := .int 7)) (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_4 (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_5 (v := .int 7) (by simp) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  refine .trans ?_ (dwp_step_6 (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst d₀) 1) 3) 5) (ℓₗ := ℓₗ) (by omega))
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l [Hℓₗ]
  · iexact Hℓₗ
  iintro Hℓₗ
  uwp_left  SPure.uwpL .frameEmp (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- This is now the last block.
  -- Left:
  -- - Exit the loop
  -- - Evaluate the var
  -- - Evaluate the deref_store
  -- Right
  -- - Evaluate the var
  -- - Evaluate the deref_store

  wp_desync
  uwp_left  SPure.uwpL .loopExit (by simp)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left  EPLift.uwpL EPLift.ret_arg <| EELift.ewpL EELift.deref_store <| EPure.ewpL <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓₗ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right EPLift.uwpR EPLift.ret_arg <| EELift.ewpR EELift.deref_store <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ)
  iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left  EPLift.uwpL EPLift.ret_arg <| ewp.deref_storeL (ChipIndex.sbufUnboundedIndex ℓₗ) (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst d₀) 1) 3) 5) 7)
  iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l [Hℓₗ]
  · iexact Hℓₗ
  iintro Hℓₗ
  uwp_right EPLift.uwpR EPLift.ret_arg <| ewp.deref_storeR (ChipIndex.sbufUnboundedIndex ℓᵣ) (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst d₀) 1) 3) 5) 7)
  iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l [Hℓᵣ]
  · iexact Hℓᵣ
  iintro Hℓᵣ
  wp_resync

  -- Perform the returns
  iintro -
  wp_desync
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync

  -- Compare the returned values for equality
  wp_sync_val
  unfold ΦPure
  ipure_intro
  grind

end example13




namespace example14
/-! Example: Loop equivalence -/


section LoopRelSyncDefs

/-- State of the iterator throughout the induction -/
@[simp] def AffineIter.st (i : AffineIter) (pk : Int) (num : Nat) := { i with peek := pk, num := num }
theorem AffineIter.eq_st_init (i : AffineIter) : i = AffineIter.st i i.peek i.num := rfl

/-- The last `num` elements of i's list -/
def IHpres  (i : AffineIter) (num : Nat) : List (NML.Value DataT) :=
  i.asList |>.drop (i.num - num)

omit [NMLEnv DataT]
theorem st_zero_asList : (AffineIter.st i pk 0).asList (DataT := DataT) = [NML.Value.int pk] := by simp

/-- The first `num` elements -/
def IHposts (i : AffineIter) (num : Nat) : List (NML.Value DataT) :=
  i.asList |>.take (i.num - num)

variable (IPre IPost : @Value DataT → PROP DataT)

def IHpreP (i : AffineIter) (num : Nat) : @PROP (DataT) :=
  iprop([∗] (IHpres i num |>.map IPre))

def IHpostP (i : AffineIter) (num : Nat) : @PROP (DataT) :=
  iprop([∗] (IHposts i num |>.map IPost))

theorem bigsep_singleton {P : PROP DataT} : iprop([∗] [P]) = P := by simp [bigSep, Std.bigOp]

end LoopRelSyncDefs
-- set_option maxHeartbeats 1000000
-- set_option pp.notation false
open TensorLib.Iterator in
-- Loop rule to demonstrate separating conjunction
-- For programs that are sampling from the same affine iterator,
-- two loops can be related provided
--   - We can separate the resources out to each value of the iterate
--   - The values of the iterates are verified independently
--   - Side conditions like the loops being simple
def wpAffineLoopRelSync' [NMLEnv DataT] {p1 p2 : List (NML.Stmt DataT)} {locL locR} {FL FR} {xL xR}
      {i : AffineIter} {j : Nat} (Hij : j ≤ i.num) {pk : Int}
      {bl br : String} {Φ : Value DataT → Value DataT → @PROP DataT}
      (IPre IPost : @Value DataT → @PROP DataT) (HK : 1 < K) :
    ⌜ locL.it iL = .some (Iterator.mk AffineIter <| AffineIter.st i pk j) ⌝ ∗
    ⌜ locR.it iR = .some (Iterator.mk AffineIter <| AffineIter.st i pk j) ⌝ ∗
    (([∗] ((AffineIter.st i pk j).asList |>.map IPost)) -∗ wp K ⟨.run ⟨pL, locL⟩, FL⟩ ⟨.run ⟨pR, locR⟩, FR⟩ Φ) ∗
    (□ ∀ v, IPre v -∗
      wp K
        ⟨.run ⟨bL, locL.bindv xL v⟩, []⟩
        ⟨.run ⟨bR, locR.bindv xR v⟩, []⟩
        (iprop(⌜· = .kont⌝ ∗ ⌜· = .kont⌝ ∗ IPost v))) ∗
    ([∗] ((AffineIter.st i pk j).asList |>.map IPre))
    ⊢ wp K
        ⟨.run ⟨.loop xL (.val <| .iref iL) bL :: pL, locL⟩, FL⟩
        ⟨.run ⟨.loop xR (.val <| .iref iR) bR :: pR, locR⟩, FR⟩
        Φ := by
  -- Proof: By regular induction on the progress of the iterator
  -- Invariant: Access to the postconditions of all loops done so far, and the preconditions
  -- of the loops not done yet.
  -- For the inductive step:

  revert pk
  -- Induction over j
  induction j
  · intro pk
    -- There is exactly one iterate remaining
    rw [st_zero_asList]; simp only [List.map_cons, List.map_nil, bigsep_singleton]
    iintro ⟨%HLocL, %HLocR, Hcont, □Hwp, Hpre⟩
    have HContL : PLoopContinue locL iL (NML.Value.int pk) := by
      unfold PLoopContinue; unfold LocalContext.peeki
      rw [HLocL]; rfl
    have HContR : PLoopContinue locR iR (NML.Value.int pk) := by
      unfold PLoopContinue; unfold LocalContext.peeki
      rw [HLocR]; rfl
    wp_desync

    -- TODO: Tactic
    have X := dwpL (SPure.uwpL (.loopContinue (x := xL) (b := bL) (ps := pL) (F := FL)) HContL)
      (Lx := K) (Lm := 1) (Rx := K) (Rm := 1)
      (pr := ⟨ExecState.run (Stmt.loop xR (Expr.val (Value.iref iR)) bR :: pR, locR), FR⟩)
      (Φ := (iprop(wp K · · Φ))) (by simp; omega)
    refine .trans ?_ X; clear X
    simp only [SPure.uwpL]
    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    have X := dwpR (SPure.uwpR (.loopContinue (x := xR) (b := bR) (ps := pR) (F := FR)) HContR)
      (Lx := K - 1) (Lm := 0) (Rx := K) (Rm := 1)
      (pl :=
      { current := ExecState.run (bL, locL.bindv xL (NML.Value.int pk)),
        context := (Stmt.loop xL (Expr.val (Value.iref iL)) bL :: pL, locL.nexti iL) :: FL }
      )
      (Φ := (iprop(wp K · · Φ))) (by simp; omega)
    refine .trans ?_ X; clear X
    simp only [SPure.uwpR]
    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    clear HContL
    clear HContR

    wp_resync

    -- -- Now, use the frame stepping rule to verify the first step of the loop
    refine .trans ?_ (wpFrameSync ?G1 ?G2 ?G3)
    case G1 => omega
    case G2 => sorry
    case G3 => sorry

    -- Specialize Hwp
    refine .trans (sep_mono (sep_mono .rfl intuitionistically_elim) .rfl) ?_
    iintro ⟨⟨Hcont, Hwp⟩, HHpre⟩
    ispecialize Hwp (NML.Value.int pk) HHpre
    istop

    -- Apply wp using monotonicity
    refine .trans (wpMono _) ?_
    istart
    iintro IH
    refine .trans ?_ (wpMonoPost (P := fun x1 x2 =>
      iprop((⌜x1 = Value.kont⌝ ∗ ⌜x2 = Value.kont⌝ ∗ IPost (NML.Value.int pk)) ∗
          (IPost (NML.Value.int pk) -∗
            wp K { current := ExecState.run (pL, locL), context := FL }
              { current := ExecState.run (pR, locR), context := FR } Φ))))
    iintro IH
    isplit r  <;> try iexact IH
     -- Obtain the resources
    iintro vl vr ⟨⟨%Hvl, ⟨%Hvr, Hpost1⟩⟩, Hwp⟩
    isplit r; ipure_intro; trivial
    isplit r; ipure_intro; trivial
    ispecialize Hwp Hpost1

    -- Exit the loop

    have HExitL : PLoopExit (locL.nexti iL) iL := by
      unfold PLoopExit; unfold LocalContext.nexti
      rw [HLocL]
      simp [Iterator.advance, next, AffineIter.st, Option.bind, LocalContext.peeki]
      -- Probs ok
      sorry
    have HExitR : PLoopExit (locL.nexti iR) iR := by sorry

    istart
    iintro ⟨-, Hwp⟩
    wp_desync

    have X := dwpL (SPure.uwpL (.loopExit (x := xL) (b := bL) (ps := pL) (F := FL)) HExitL)
      (Lx := K) (Lm := 1) (Rx := K) (Rm := 1)
      (pr := { current := ExecState.run (Stmt.loop xR (Expr.val (Value.iref iR)) bR :: pR, locR.nexti iR), context := FR })
      (Φ := (iprop(wp K · · Φ))) (by simp; omega)
    refine .trans ?_ X; clear X
    simp only [SPure.uwpL, Nat.sub_self]
    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    have X := dwpR (SPure.uwpR (.loopExit (x := xR) (b := bR) (ps := pR) (F := FR)) HExitR)
      (Lx := K - 1) (Lm := 0) (Rx := K) (Rm := 1)
      (pl := { current := ExecState.run (pL, locL.nexti iL), context := FL })
      (Φ := (iprop(wp K · · Φ))) (by simp; omega)
    simp only [SPure.uwpR] at X
    refine (.trans ?_
      (Q := (sep (BI.pure True)
      (wand (BI.pure True)
        (dwp 0 (HSub.hSub 1 1) (HSub.hSub K 1) (HSub.hSub K 1)
          { current := ExecState.run (Prod.mk pL (locL.nexti iL)), context := FL }
          { current := ExecState.run (Prod.mk pR (locL.nexti iR)), context := FR } fun x1 x2 => wp K x1 x2 Φ))))
      ?G)
    case G => sorry -- It's X, but I'm getting defeq timeouts now
    clear X

    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    wp_resync
    -- Clean up hypothesis so that it takes locL with i bound to none
    sorry


  · rename_i n pk


    sorry


  /-

  -- Clean up some of the spec
  generalize HwpDef : iprop(□ ∀ v, IPre v -∗
      wp K ⟨.run (bL, locL.bindv xL v), []⟩ ⟨.run (bR, locR.bindv xR v), []⟩
      (iprop(⌜· = Value.kont⌝ ∗ ⌜· = Value.kont⌝ ∗ IPost v))) = Hwp

  -- 1. Destruct i and tidy up the proof state
  rcases i with ⟨ist, ipk, inum, istn, istep⟩
  let I inum ipk := (⟨ist, ipk, inum, istn, istep⟩ : AffineIter)
  obtain X : ⟨ist, ipk, inum, istn, istep⟩ = I inum ipk := by rfl
  rw [X]; clear X
  let II inum ipk : Iterator DataT := Iterator.mk AffineIter (I inum ipk)
  obtain X : Iterator.mk AffineIter (I inum ipk) = II inum ipk := by rfl
  rw [X]; clear X
  iintro ⟨%HiLeft, %HiRight, _⟩; istop
  let inum_init := inum
  let InvPre inum ipk : PROP DataT := [∗] (List.map IPre (toList (I inum_init ipk) |>.take inum))
  -- TODO: Lemma about toList of affineiter
  obtain X : iprop([∗] (List.map IPre (toList (I inum ipk)))) = InvPre inum ipk := by
    sorry
  rw [X]; clear X
  let InvPost inum ipk : PROP DataT := [∗] (List.map IPost (toList (I inum ipk) |>.drop inum))
  obtain X : iprop(emp) = InvPost inum ipk := by
    sorry
  refine .trans emp_sep.mpr ?_
  rw [X]; clear X
  let Hcont inum ipk : PROP DataT := iprop([∗] (List.map IPost (toList (I inum ipk))) -∗ wp K { current := ExecState.run (pL, locL), context := FL } { current := ExecState.run (pR, locR), context := FR } Φ)
  have X : iprop([∗] (List.map IPost (toList (I inum ipk))) -∗ wp K { current := ExecState.run (pL, locL), context := FL } { current := ExecState.run (pR, locR), context := FR } Φ) = Hcont inum ipk := rfl
  rw [X]; clear X
  revert ipk
  induction inum

  -- Perform induction
  · intro ipk
    intro HlocL HlocR
    iintro ⟨Hpost, Hcont, -, -⟩
    -- No steps left

    wp_desync

    -- uwp_left  SPure.uwpL .loopExit Hloop
    have X :=
      dwpL (SPure.uwpL (@SPure.loopExit DataT _ xL iL bL pL locL FL) ?G1) (Lx := K) (Lm := 1) (Rx := K) (Rm := 1)
        (pr := ⟨ExecState.run (Stmt.loop xR (Expr.val (Value.iref iR)) bR :: pR, locR), FR⟩) (Φ := (iprop(wp K · · Φ))) ?G2
    case G1 => sorry
    case G2 => sorry
    refine .trans ?_ X; clear X
    simp [SPure]
    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    have X :=
      dwpR (SPure.uwpR (@SPure.loopExit DataT _ xR iR bR pR locR FR) ?G1) (Lx := K - 1) (Lm := 0) (Rx := K) (Rm := 1)
        (pl := ⟨ExecState.run (pL, locL), FL⟩)  (Φ := (iprop(wp K · · Φ))) ?G2
    case G1 => sorry
    case G2 => sorry
    refine .trans ?_ X; clear X
    simp [SPure]
    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    refine Entails.trans ?_ <| wand_entails <| wpResync

    iintro ⟨Hpost, Hcont⟩
    iapply Hcont
    unfold InvPost
    rw [List.drop_zero]
    iexact Hpost

  · intro ipk HiLeft HiRight
    rename_i iph IH

    -- Step both sides to get a frame
    -- wpFrameSync' with mono to frame the resources
    -- Need to unvold InvPost and InvPre

    sorry
  -/


end example14




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
