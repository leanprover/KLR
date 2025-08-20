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

@[simp] def sL : ProgState DataT := ⟨.run ⟨[
    .assign (some "ℓ") (.alloc .sbuf),
    .mkiter 1 (.affineRange 1 2 3),
    .tsdunop (.var "ℓ") .cst (.val <| .int 0),
    .loop "z" (.val <| .iref 1) [
      .tsdunop (.var "ℓ") .add (.var "z"),
    ],
    .ret <| (.deref_store (.var "ℓ")),
  ], .emp⟩, []⟩

@[simp] def sR : ProgState DataT := ⟨.run ⟨[
    .assign (some "ℓ") (.alloc .sbuf),
    .tsdunop (.var "ℓ") .cst (.val <| .int 0),
    .tsdunop (.var "ℓ") .add (.val <| .int 1),
    .tsdunop (.var "ℓ") .add (.val <| .int 3),
    .tsdunop (.var "ℓ") .add (.val <| .int 5),
    .tsdunop (.var "ℓ") .add (.val <| .int 7),
    .ret <| (.deref_store (.var "ℓ")),
  ], .emp⟩, []⟩

attribute [local simp] LocalContext.emp Iterators.emp Iterators.bind Iterator.peek
  TensorLib.Iterator.peek IteratorS.toIterator Option.bind Iterator.advance


example : ⊢ wp (DataT := DataT) 7 sL sR (ΦPure (· = ·)) := by
  istart
  -- First desync block:
  -- - Step the left and right sides to allocate the variable ℓ
  -- - Step the left side to allocate the iterator
  -- - Step the left and right sides to apply the zeroing dunop
  wp_desync
  dwp_left   dwpAllocL; iintro ℓₗ Hℓ₁
  dwp_right  dwpAllocR; iintro Hℓₗ ℓᵣ Hℓᵣ
  uwp_left   SPure.uwpL .mkiter trivial; iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left   EPLift.uwpL EPLift.tsdunop_loc <| EPure.ewpL <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓₗ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right  EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopLCst (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l   [Hℓₗ]; iexact Hℓₗ; iintro Hℓₗ
  dwp_right  (dwpTSDunopRCst (by omega)); iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l   [Hℓᵣ]; iexact Hℓᵣ; iintro Hℓₗ
  wp_resync

  -- Loop desync blocks:
  -- Left:
  --   - Open the loop body
  --   - Step the var from "ℓ" to the pointer
  --   - Step the value from "z" to the integer
  --   - Step the tsdunop statement
  --   - Close the loop body
  -- Right:
  --   - Step the var from "ℓ" to the pointer
  --   - Step the tsdunop statement
  wp_desync; iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right  EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddR (s := TSDunop.app_cst (NMLEnv.intoDataT 0)) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l   [Hℓᵣ]; iexact Hℓᵣ; iintro Hℓᵣ
  uwp_left   SPure.uwpL (.loopContinue (v := .int 1)) (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddLocL  (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddValL (v := .int 1) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddL  (s := TSDunop.app_cst (NMLEnv.intoDataT 0)) (ℓₗ := ℓₗ) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l   [Hℓₗ]; iexact Hℓₗ; iintro Hℓₗ
  uwp_left   SPure.uwpL .frameEmp (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- Do the block again
  wp_desync; iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right  EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_right  (dwpTSDunopAddR (s := TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) (by omega)); iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l   [Hℓᵣ]; iexact Hℓᵣ; iintro Hℓᵣ
  uwp_left   SPure.uwpL (.loopContinue (v := .int 3)) (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddLocL (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddValL  (v := .int 3) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddL  (s := TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) (ℓₗ := ℓₗ) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l   [Hℓₗ]; iexact Hℓₗ; iintro Hℓₗ
  uwp_left   SPure.uwpL .frameEmp (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- Do the block again
  wp_desync; iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right  EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_right  (dwpTSDunopAddR (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) 3) (by omega)); iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l   [Hℓᵣ]; iexact Hℓᵣ; iintro Hℓᵣ
  uwp_left   SPure.uwpL (.loopContinue (v := .int 5)) (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddLocL (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddValL (v := .int 5) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddL   (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) 3) (ℓₗ := ℓₗ) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l   [Hℓₗ]; iexact Hℓₗ; iintro Hℓₗ;
  uwp_left   SPure.uwpL .frameEmp (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  wp_resync
  rw [Iterators.bind_bind]

  -- Do the block again
  wp_desync; iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right  EPLift.uwpR EPLift.tsdunop_loc <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_right  (dwpTSDunopAddR (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) 3) 5) (by omega)); iintro ⟨Hℓᵣ, Hℓₗ⟩;
  isplit l   [Hℓᵣ]; iexact Hℓᵣ; iintro Hℓᵣ
  uwp_left   SPure.uwpL (.loopContinue (v := .int 7)) (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddLocL  (v := .uptr <| ChipIndex.sbufUnboundedIndex ℓₗ) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddValL (v := .int 7) (by simp) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  dwp_left   (dwpTSDunopAddL   (s := TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) 3) 5) (ℓₗ := ℓₗ) (by omega)); iintro ⟨Hℓₗ, Hℓᵣ⟩
  isplit l   [Hℓₗ]; iexact Hℓₗ; iintro Hℓₗ
  uwp_left   SPure.uwpL .frameEmp (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
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
  uwp_left   SPure.uwpL .loopExit (by simp); iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left   EPLift.uwpL EPLift.ret_arg <| EELift.ewpL EELift.deref_store <| EPure.ewpL <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓₗ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_right  EPLift.uwpR EPLift.ret_arg <| EELift.ewpR EELift.deref_store <| EPure.ewpR <| EPure.var (v := .uptr <| .sbufUnboundedIndex ℓᵣ); iintro ⟨Hℓₗ, Hℓᵣ⟩
  uwp_left   EPLift.uwpL EPLift.ret_arg <| ewp.deref_storeL (ChipIndex.sbufUnboundedIndex ℓₗ) (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) 3) 5) 7); iintro ⟨Hℓᵣ, Hℓₗ⟩
  isplit l   [Hℓₗ]; iexact Hℓₗ; iintro Hℓₗ
  uwp_right  EPLift.uwpR EPLift.ret_arg <| ewp.deref_storeR (ChipIndex.sbufUnboundedIndex ℓᵣ) (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_addZ (TSDunop.app_cst (NMLEnv.intoDataT 0)) 1) 3) 5) 7)
  iintro ⟨Hℓᵣ, Hℓₗ⟩; isplit l [Hℓᵣ]; iexact Hℓᵣ
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



/-
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
    case G2 => s orry
    case G3 => s orry

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
      s orry
    have HExitR : PLoopExit (locL.nexti iR) iR := by s orry

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
    case G => so rry -- It's X, but I'm getting defeq timeouts now
    clear X

    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    wp_resync
    -- Clean up hypothesis so that it takes locL with i bound to none
    s orry


  · rename_i n pk


    s orry


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
    s orry
  rw [X]; clear X
  let InvPost inum ipk : PROP DataT := [∗] (List.map IPost (toList (I inum ipk) |>.drop inum))
  obtain X : iprop(emp) = InvPost inum ipk := by
    s orry
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
    case G1 => s orry
    case G2 => s orry
    refine .trans ?_ X; clear X
    simp [SPure]
    istart; iintro H
    isplit r; exact true_intro
    iintro -; istop

    have X :=
      dwpR (SPure.uwpR (@SPure.loopExit DataT _ xR iR bR pR locR FR) ?G1) (Lx := K - 1) (Lm := 0) (Rx := K) (Rm := 1)
        (pl := ⟨ExecState.run (pL, locL), FL⟩)  (Φ := (iprop(wp K · · Φ))) ?G2
    case G1 => s orry
    case G2 => s orry
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

    s orry
  -/

end example14
-/

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
-- Unbounded loop rule

-- Open questions:
-- Composition (seq rule for frame steps)
-- Monotonicity of K
-- Improved surface syntax
-- Better timeout on the tactics
-- ret_assert and adequacy
