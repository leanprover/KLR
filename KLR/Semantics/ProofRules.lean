/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Logic
import KLR.Semantics.SmallStep

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML

variable {DataT : Type _}

/-- Value-value rule: base case for the proof -/
theorem wpValVal {c1 c2 : @prog DataT × @state DataT} {v1 v2 : val} {Φ : val → val → @PROP DataT} {K}
    (H1 : to_val c1.1 = some v1) (H2 : to_val c2.1 = some v2) :
    Φ v1 v2 ⊢ wp K c1.1 c2.1 Φ := by
  -- Unfold the WP
  refine Entails.trans ?_ (Q := ?_) ?G1
  case G1 =>
    apply (Iris.BI.equiv_iff.mp ?G2).mp
    case G2=> exact (@wp_unfold DataT K c1.fst c2.fst Φ).symm
    -- Weird unification bug?

  -- Enter the left case
  istart; iintro H; ileft; istop

  -- Eliminate the update
  refine Entails.trans BIUpdate.intro (Q := iprop(|==> Φ v1 v2)) (BIUpdate.mono ?_)

  -- Specialize the exists and conclude
  istart
  iintro H
  iexists v1
  iexists v2
  isplit r; ipure_intro; exact H1
  isplit r; ipure_intro; exact H2
  iexact H

-- TODO: Make a more general (pureN/pureM) tactic
theorem wpPureSync {p1 p2 p1' p2' : @prog DataT} {Φ : @val DataT → @val DataT → @PROP DataT} {K : LeibnizO Nat}
    -- The left hand side takes a pure step
    (H1 : ∀ s : @State DataT, (NMLSemantics DataT).Step (p1, s) (p1', s))
    -- The right hand side takes a pure step
    (H2 : ∀ s : @State DataT, (NMLSemantics DataT).Step (p2, s) (p2', s))
    (Hk : 1 ≤ K.car) :
    wp K p1' p2' Φ ⊢ wp K p1 p2 Φ := by
  -- Unfold the WP
  refine Entails.trans ?_ (Q := ?_) ?G1
  case G1 =>
    apply (Iris.BI.equiv_iff.mp ?G2).mp
    case G2=> exact (@wp_unfold DataT K p1 p2 Φ).symm
    -- Weird unification bug?

  -- Enter the right case, get state resources, set step numbers
  istart
  iintro H
  iright
  iintro sl sr Hs
  iexists (p1', sl)
  iexists (p2', sr)
  iexists 1
  iexists 1
  isplit r
  · ipure_intro
    refine ⟨Nat.one_pos, Nat.one_pos, Hk, Hk, ?_, ?_⟩
    · exact (NMLSemantics DataT).stepN_1_iff_step.mpr (H1 _)
    · exact (NMLSemantics DataT).stepN_1_iff_step.mpr (H2 _)
  istop

  -- Eliminate the later
  refine Entails.trans ?_ Iris.BI.later_intro
  refine Entails.trans ?_ Iris.BIUpdate.intro

  -- Close using the remaining resources
  istart
  iintro ⟨Hwp, Hstate⟩
  isplit l [Hstate]
  · iexact Hstate
  · iexact Hwp

-- TODO: Port updates for heaps
theorem update_lemma (σₗ σᵣ : @state DataT) :
  state_interp σₗ σᵣ ⊢
    |==> ∃ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ ∗ ℓᵣ [S]⇉ᵣ∅ ∗
    state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩ :=
  sorry

theorem wpAllocSync  {Φ : @val DataT → @val DataT → @PROP DataT} {K : LeibnizO Nat}
    (Hk : 1 ≤ K.car) :
     (∀ ℓₗ ℓᵣ, (ℓₗ [S]⇉ₗ∅) -∗ (ℓᵣ [S]⇉ᵣ∅) -∗ wp K (.run <| p1) (.run <| p2) Φ) ⊢
     wp K
       (.run <| ⟨.assign none (.alloc Memory.sbuf), locₗ⟩ :: p1)
       (.run <| ⟨.assign none (.alloc Memory.sbuf), loc₂⟩ :: p2)
       Φ := by
  refine Entails.trans ?_ (Q := ?_) ?G1
  case G1 =>
    apply (Iris.BI.equiv_iff.mp ?G2).mp
    case G2=> exact (@wp_unfold DataT K _ _ Φ).symm
  iintro ⟨Hrec⟩
  iright
  iintro σₗ σᵣ
  iintro Hσ
  iexists (.run p1, ⟨ChipMemory.freshSBUFStore σₗ.memory |>.2⟩)
  iexists (.run p2, ⟨ChipMemory.freshSBUFStore σᵣ.memory |>.2⟩)
  iexists 1
  iexists 1
  isplit r
  · ipure_intro
    simp [Hk]
    refine ⟨?_, ?_⟩
    · apply (NMLSemantics DataT).stepN_1_iff_step.mpr
      apply step.seq (v := Value.uptr <| ChipMemory.freshSBUFStore σₗ.memory |>.1)
      apply ExprStep.sbuf_alloc rfl
    · apply (NMLSemantics DataT).stepN_1_iff_step.mpr
      apply step.seq (v := Value.uptr <| ChipMemory.freshSBUFStore σᵣ.memory |>.1)
      apply ExprStep.sbuf_alloc rfl
  istop
  refine Entails.trans ?_ Iris.BI.later_intro
  istart
  iintro ⟨Hrec, Hσ⟩
  simp only []

  -- Apply update_lemma and eliminate the bupd
  istop
  have X := update_lemma σₗ σᵣ
  have Y := @BI.sep_mono_r (PROP := @PROP DataT) _ _ _ (P := iprop(∀ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ -∗ ℓᵣ [S]⇉ᵣ∅ -∗ wp K (ExecState.run p1) (ExecState.run p2) Φ)) X
  apply Entails.trans Y
  clear X Y
  apply Entails.trans bupd_frame_l
  refine BIUpdate.mono ?_
  istart

  iintro ⟨Hwp, ℓₗ, ℓᵣ, Hℓₗ, Hℓᵣ, Hσ⟩
  ispecialize Hwp ℓₗ ℓᵣ Hℓₗ Hℓᵣ
  isplit l [Hσ]
  · iexact Hσ
  · iexact Hwp


-- TODO: Stuttering block
-- I want to be able to take different steps on each side altogether. To do this, I want to
-- define unary rules, and a system for lifting them to a combined step.

-- This would be a good example for multi-BI proof interfaces

/-- Unary weakest precondition -/
structure UWP where
  pre  : @PROP DataT
  post : @PROP DataT
  prog : @prog DataT

def UWP.LeftSpec (u : @UWP DataT) : @PROP DataT :=
  iprop(∀ σₗ σᵣ, u.pre -∗ state_interp σₗ σᵣ -∗ ∀ prog' σₗ', ⌜step (u.prog, σₗ) (prog', σₗ')⌝ -∗ |==> (state_interp σₗ' σᵣ ∗ u.post))

def UWP.RightSpec (u : @UWP DataT) : @PROP DataT :=
  iprop(∀ σₗ σᵣ, u.pre -∗ state_interp σₗ σᵣ -∗ ∀ prog' σᵣ', ⌜step (u.prog, σᵣ) (prog', σᵣ')⌝ -∗ |==> (state_interp σₗ σᵣ' ∗ u.post))

def UWP.Frame (u : @UWP DataT) (P : @PROP DataT) : @UWP DataT where
  pre  := iprop(u.pre  ∗ P)
  post := iprop(u.post ∗ P)
  prog := u.prog

theorem UWP.leftSpec_frame {u : @UWP DataT} :
    u.LeftSpec ⊢ (u.Frame P).LeftSpec := by
  simp only [Frame, LeftSpec]
  istart
  iintro Hspec σₗ σᵣ ⟨Hu, HP⟩ Hσ prog' σₗ' Hstep
  ispecialize Hspec σₗ σᵣ Hu Hσ prog' σₗ' Hstep
  istop
  have L1 : P ∗ |==> (state_interp σₗ' σᵣ ∗ u.post) ⊢ |==> (state_interp σₗ' σᵣ ∗ u.post ∗ P) := by
    apply Entails.trans BI.sep_comm.mp
    apply Entails.trans BIUpdate.frame_r _
    refine BIUpdate.mono BI.sep_assoc_l
  apply Entails.trans _ L1; clear L1
  istart
  iintro ⟨HP, Hwp⟩
  isplit l [HP]
  · iexact HP
  · iexact Hwp

theorem UWP.rightSpec_frame {u : @UWP DataT} :
    u.RightSpec ⊢ (u.Frame P).RightSpec := by
  simp only [Frame, RightSpec]
  istart
  iintro Hspec σₗ σᵣ ⟨Hu, HP⟩ Hσ prog' σᵣ' Hstep
  ispecialize Hspec σₗ σᵣ Hu Hσ prog' σᵣ' Hstep
  istop
  have L1 : P ∗ |==> (state_interp σₗ σᵣ' ∗ u.post) ⊢ |==> (state_interp σₗ σᵣ' ∗ u.post ∗ P) := by
    apply Entails.trans BI.sep_comm.mp
    apply Entails.trans BIUpdate.frame_r _
    refine BIUpdate.mono BI.sep_assoc_l
  apply Entails.trans _ L1; clear L1
  istart
  iintro ⟨HP, Hwp⟩
  isplit l [HP]
  · iexact HP
  · iexact Hwp

structure Stutter where
  lwp : List (@UWP DataT)
  rwp : List (@UWP DataT)
