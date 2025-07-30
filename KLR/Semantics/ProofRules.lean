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
theorem wpValVal {p1 p2 : ExecState DataT } {v1 v2 : NML.Value DataT} {Φ : NML.Value DataT → NML.Value DataT → PROP DataT} {K}
    (H1 : toVal p1 = some v1) (H2 : toVal p2 = some v2) :
    Φ v1 v2 ⊢ wp K p1 p2 Φ := by
  -- Unfold the WP
  refine Entails.trans ?_ (Q := ?_) ?G1
  case G1 =>
    apply (Iris.BI.equiv_iff.mp ?G2).mp
    case G2=> exact (@wp_unfold DataT K p1 p2 Φ).symm
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

theorem wpPureSync {p1 p2 p1' p2' : ExecState DataT} {Φ : NML.Value DataT → NML.Value DataT → @PROP DataT} {K : LeibnizO Nat}
    (H1 : SmallStep.PureStep p1 p1')
    (H2 : SmallStep.PureStep p2 p2')
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
  istop
  apply Entails.trans _ BIUpdate.intro
  istart
  iintro ⟨Hwp, Hs⟩
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

  -- Close using the remaining resources
  istart
  iintro ⟨Hwp, Hstate⟩
  isplit l [Hstate]
  · iexact Hstate
  · iexact Hwp



-- TODO: Port updates for heaps
theorem update_lemma (σₗ σᵣ : NML.State DataT) :
  state_interp σₗ σᵣ ⊢
    |==> (∃ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ ∗ ℓᵣ [S]⇉ᵣ∅ ∗
    state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩) :=
  sorry

theorem wpAllocSync  {Φ : NML.Value DataT → NML.Value DataT → @PROP DataT} {K : LeibnizO Nat}
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

  -- Apply update_lemma and eliminate the bupd
  istop
  have X := update_lemma σₗ σᵣ
  have Y := @BI.sep_mono_r (PROP := @PROP DataT) _ _ _ (P := iprop(∀ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ -∗ ℓᵣ [S]⇉ᵣ∅ -∗ wp K (ExecState.run p1) (ExecState.run p2) Φ)) X
  apply Entails.trans Y
  clear X Y
  apply Entails.trans bupd_frame_l
  refine BIUpdate.mono ?_
  istart


  iintro ⟨Hrec⟩
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
  iintro ⟨Hwp, ℓₗ, ℓᵣ, Hℓₗ, Hℓᵣ, Hσ⟩
  simp only []
  ispecialize Hwp ℓₗ ℓᵣ Hℓₗ Hℓᵣ
  isplit l [Hσ]
  · iexact Hσ
  · iexact Hwp

/-- Unary weakest precondition

-/
structure UWP (DataT : Type _) where
  pre   : PROP DataT
  post  : PROP DataT
  prog  : ExecState DataT
  steps : Nat

def UWP.LeftSpec (u : UWP DataT) : PROP DataT :=
  iprop(∀ σₗ σᵣ, u.pre -∗ state_interp σₗ σᵣ -∗
    ∀ prog' σₗ', ⌜SmallStep.StepN u.steps (u.prog, σₗ) (prog', σₗ')⌝ -∗ |==> (state_interp σₗ' σᵣ ∗ u.post))

def UWP.RightSpec (u : UWP DataT) : PROP DataT :=
  iprop(∀ σₗ σᵣ, u.pre -∗ state_interp σₗ σᵣ -∗
    ∀ prog' σᵣ', ⌜SmallStep.StepN u.steps (u.prog, σᵣ) (prog', σᵣ')⌝ -∗ |==> (state_interp σₗ σᵣ' ∗ u.post))

def UWP.Frame (u : UWP DataT) (P : PROP DataT) : UWP DataT where
  pre   := iprop(u.pre  ∗ P)
  post  := iprop(u.post ∗ P)
  prog  := u.prog
  steps := u.steps

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


-- def awp (Lm Rm Lx Rx : Nat) (p1 p2 : ExecState DataT) (Φ : ExecState DataT → ExecState DataT → @PROP DataT) :
--     @PROP DataT :=
--   iprop(∀ sl, ∀ sr, state_interp sl sr -∗
--           ∃ cl', ∃ cr', ∃ nl, ∃ nr,
--           ⌜Lm ≤ nl ∧ Rm ≤ nr ∧ nl ≤ Lx ∧ nr ≤ Rx ∧ SmallStep.StepN nl (p1, sl) cl' ∧ SmallStep.StepN nr (p2, sr) cr'⌝ ∗
--           |==> (state_interp cl'.2 cr'.2 ∗ Φ cl'.1 cr'.1))

def awp (Lm Rm Lx Rx : Nat) (p1 p2 : ExecState DataT) (Φ : ExecState DataT → ExecState DataT → @PROP DataT) :
    @PROP DataT :=
  iprop(∀ s1, ∀ s2, state_interp s1 s2 -∗ |==>
          ∃ p1' p2',
            Φ p1' p2' ∗
            ∃ s1' s2',
              (∃ nl nr, ⌜Lm ≤ nl ∧ Rm ≤ nr ∧ nl ≤ Lx ∧ nr ≤ Rx ∧ SmallStep.StepN nl (p1, s1) (p1', s1') ∧ SmallStep.StepN nr (p2, s2) (p2', s2')⌝ ) ∗
              state_interp s1' s2')


theorem wpDesync {K : LeibnizO Nat} {p1 p2 : ExecState DataT} (Φf : NML.Value DataT → NML.Value DataT → @PROP DataT) :
    ⊢ awp 1 1 K.1 K.1 p1 p2 (wp K · · Φf) -∗ wp K p1 p2 Φf := by
  refine Entails.trans ?_ (Q := iprop((awp 1 1 K.car K.car p1 p2 fun x1 x2 => wp K x1 x2 Φf) -∗ ?_)) ?G1
  case G1 =>
    apply BI.wand_mono BI.entails_preorder.refl
    apply (Iris.BI.equiv_iff.mp ?G2).mp
    case G2=> exact (@wp_unfold DataT K p1 p2 _).symm
  unfold awp
  iintro Hawp
  iright
  iintro sl sr Hσ
  ispecialize Hawp sl sr Hσ

  istop
  apply Iris.BI.BIBase.Entails.trans Iris.BI.emp_sep.mp
  refine BIUpdate.mono ?_
  istart
  iintro ⟨Hawp⟩


  icases Hawp with ⟨p1', p2', Hwp, s1', s2', ⟨n1, n2, %Hstep⟩, Hupd⟩
  simp only []
  -- Eliminate all bupds
  iexists (p1', s1')
  iexists (p2', s2')
  iexists n1
  iexists n2
  isplit r
  · ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, by trivial⟩ <;> try omega
  istop
  refine Entails.trans ?_ Iris.BI.later_intro
  simp only []
  istart
  iintro ⟨Hwp, Hs⟩
  isplit l [Hs]
  · iexact Hs
  · iexact Hwp
  -- icases Hawp with ⟨cl', cr', nl, nr, %Hstep, H⟩
  -- iexists cl'
  -- iexists cr'
  -- iexists nl
  -- iexists nr
  -- isplit r
  -- · ipure_intro
  --   obtain ⟨_, _, _, _, _, _⟩ := Hstep
  --   refine ⟨?_, ?_, ?_, ?_, by trivial⟩ <;> try omega
  -- -- Eliminate the later and bupd
  -- istop
  -- refine Entails.trans ?_ Iris.BI.later_intro
  -- refine BIUpdate.mono ?_
  -- simp only []
  -- istart
  -- apply BI.entails_wand .rfl

theorem wpResync {m' n' : Nat} {p1 p2 : ExecState DataT} (Φ : ExecState DataT → ExecState DataT → @PROP DataT) :
    ⊢ Φ p1 p2 -∗ awp 0 0 m' n' p1 p2 Φ := by
  unfold awp
  iintro HΦ s1 s2 Hσ
  istop
  apply Entails.trans _ BIUpdate.intro
  istart
  iintro ⟨HΦ, Hσ⟩
  iexists p1
  iexists p2
  isplit l [HΦ]
  · iexact HΦ
  iexists s1
  iexists s2
  isplit r
  · iexists 0
    iexists 0
    ipure_intro
    simp only [Nat.le_refl, Nat.zero_le, true_and]
    refine ⟨SmallStep.StepN.done rfl, SmallStep.StepN.done rfl⟩
  iexact Hσ

  -- iexists ⟨p1, s1⟩
  -- iexists ⟨p2, s2⟩
  -- iexists 0
  -- iexists 0
  -- isplit r
  -- · ipure_intro
  --   simp only [Nat.le_refl, Nat.zero_le, true_and]
  --   refine ⟨SmallStep.StepN.done rfl, SmallStep.StepN.done rfl⟩

  -- -- Eliminate the later and bupd
  -- istop
  -- refine Entails.trans ?_ BIUpdate.intro
  -- simp only []
  -- istart
  -- iintro ⟨HΦ, Hσ⟩

  -- isplit l [Hσ]
  -- · iexact Hσ
  -- · iexact HΦ


theorem awpPureL (Hstep : SmallStep.PureStep p1 p1') (Hx : 0 < Lx := by omega) :
    ⊢ awp (Lm - 1) Rm (Lx - 1) Rx p1' p2 Φ -∗ awp Lm Rm Lx Rx p1 p2 Φ := by
  simp at Hx
  istart
  unfold awp
  iintro Hawp
  iintro sl sr Hσ
  ispecialize Hawp sl sr Hσ
  istop
  apply Iris.BI.BIBase.Entails.trans Iris.BI.emp_sep.mp
  apply BIUpdate.mono _
  istart
  iintro ⟨Hawp⟩
  icases Hawp with ⟨p1', p2', HΦ, s1', s2', ⟨nl, nr, %Hstep⟩, Hstate⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists s1'
  iexists s2'
  isplit r
  · iexists (nl + 1)
    iexists nr
    ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    refine SmallStep.StepN.step (Hstep sl) ?_
    trivial
  · iexact Hstate
  -- icases Hawp with ⟨cl', cr', nl, nr, %Hstep', H⟩
  -- iexists cl'
  -- iexists cr'
  -- iexists (nl + 1)
  -- iexists nr
  -- isplit r
  -- · ipure_intro
  --   obtain ⟨_, _, _, _, _, _⟩ := Hstep'
  --   refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
  --   refine SmallStep.StepN.step (Hstep sl) ?_
  --   trivial
  -- istop
  -- refine BIUpdate.mono .rfl

theorem awpPureR (Hstep : SmallStep.PureStep p2 p2') (Hx : 0 < Rx := by omega) :
    ⊢ awp Lm (Rm - 1) Lx (Rx - 1) p1 p2' Φ -∗ awp Lm Rm Lx Rx p1 p2 Φ := by
  simp at Hx
  istart
  unfold awp
  iintro Hawp
  iintro sl sr Hσ
  ispecialize Hawp sl sr Hσ
  istop
  apply Iris.BI.BIBase.Entails.trans Iris.BI.emp_sep.mp
  apply BIUpdate.mono _
  istart
  iintro ⟨Hawp⟩
  icases Hawp with ⟨p1', p2', HΦ, s1', s2', ⟨nl, nr, %Hstep⟩, H⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists s1'
  iexists s2'
  isplit r [H]
  · iexists nl
    iexists (nr + 1)
    ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    refine SmallStep.StepN.step (Hstep sr) ?_
    trivial
  · iexact H
  -- icases Hawp with ⟨cl', cr', nl, nr, %Hstep', H⟩
  -- iexists cl'
  -- iexists cr'
  -- iexists nl
  -- iexists (nr + 1)
  -- isplit r
  -- · ipure_intro
  --   obtain ⟨_, _, _, _, _, _⟩ := Hstep'
  --   refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
  --   refine SmallStep.StepN.step (Hstep sr) ?_
  --   trivial
  -- istop
  -- refine BIUpdate.mono .rfl

-- -- TODO: Port updates for heaps
-- theorem update_lemma (σₗ σᵣ : NML.State DataT) :
--   state_interp σₗ σᵣ ⊢
--     |==> ∃ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ ∗ ℓᵣ [S]⇉ᵣ∅ ∗
--     state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩ :=
--   sorry


-- TODO: Unify the left and right pure/stateful desync steps with UWP?


theorem update_lemma_left (σₗ σᵣ : NML.State DataT)
      (HL : ChipMemory.get_store σₗ.memory (.sbufUnboundedIndex ℓ₁) = none):
  state_interp σₗ σᵣ ⊢ |==> ((ChipMemory.freshSBUFStore σₗ.1).1 ⇉ₗ∅ ∗ state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ σᵣ) :=
  sorry

theorem awpAllocL (Hx : 0 < Lx := by omega) :
    ⊢ (∀ ℓₗ, (ℓₗ [S]⇉ₗ∅) -∗
             awp (Lm - 1) Rm (Lx - 1) Rx (.run <| p1'.map (.bind DataT · x (.uptr <| ChipIndex.sbufUnboundedIndex ℓₗ))) p2 Φ) -∗
      awp Lm Rm Lx Rx (.run <| ⟨.assign (.some x) (.alloc Memory.sbuf), locₗ⟩ :: p1') p2 Φ := by
  simp at Hx
  istart
  iintro Hawp
  conv =>
    rhs
    unfold awp
  iintro sl sr Hs

  -- Apply update_lemma
  istop
  have X := update_lemma_left sl sr (ℓ₁ := sl.memory.sbufUnbounded.next_fresh) ?G
  case G =>
    -- Store get fresh is none
    simp [ChipMemory.get_store]
    rw [← AllocHeap.get_fresh (t := sl.memory.sbufUnbounded) (H := sl.memory.sbuf_wf)]
    rfl
  have Y := @BI.sep_mono_r (PROP := @PROP DataT) _ _
              (P := iprop((∀ ℓₗ, (ℓₗ [S]⇉ₗ∅) -∗ awp (Lm - 1) Rm (Lx - 1) Rx (.run <| p1'.map (.bind DataT · x (.uptr <| ChipIndex.sbufUnboundedIndex ℓₗ))) p2 Φ)))
              _ X
  apply Entails.trans Y
  clear X Y
  simp only []
  istart
  iintro ⟨Hawp, Hupd⟩

  istop
  apply Entails.trans bupd_frame_l
  apply Entails.trans ?_ bupd_idem.mp
  apply BIUpdate.mono
  istart
  iintro ⟨Hawp, ⟨Hfrac, Hauth⟩⟩

  obtain ⟨ℓ₁, Hℓ₁⟩ : ∃ ℓ₁ : Nat, (ChipMemory.freshSBUFStore sl.memory).fst = .sbufUnboundedIndex ℓ₁ := by
    simp

  -- Need to be very careful with the unfolding ehre
  ispecialize Hawp ℓ₁
  rw [Hℓ₁]
  ispecialize Hawp Hfrac

  unfold awp
  ispecialize Hawp { memory := (ChipMemory.freshSBUFStore sl.memory).snd } sr Hauth
  istop
  apply Iris.BI.BIBase.Entails.trans Iris.BI.emp_sep.mp
  apply BIUpdate.mono
  istart
  iintro ⟨p1', p2', HΦ, s1, s2, ⟨n1, n2, %Hstep⟩, H⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists s1
  iexists s2
  isplit r
  · iexists (n1 + 1)
    iexists n2
    ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    rename_i SL  _
    apply SmallStep.StepN.step _ SL
    apply NML.step.asn
    apply ExprStep.sbuf_alloc
    simp
    simp at Hℓ₁
    exact Hℓ₁.symm
  · iexact H
