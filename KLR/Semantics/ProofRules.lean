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
open Iris Iris.BI Iris.BI.BIBase KLR.Core Iris NML SmallStep

variable {DataT : Type _}

/-- Two values are related when they are related by Φ. -/
theorem wpValVal (H1 : toVal p1 = some v1) (H2 : toVal p2 = some v2) :
    Φ v1 v2 ⊢ wp K p1 p2 Φ := by
  -- Unfold the wp
  refine .trans ?_ (equiv_iff.mp <| wp_unfold.symm).mp
  -- Enter the left case because the programs are values
  refine .trans ?_ or_intro_l
  -- Eliminate the update (the ghost state does not need to be updated)
  refine .trans ?_ BIUpdate.intro
  -- Conclude, using the current state
  iintro HΦ
  iexists v1
  iexists v2
  isplit r
  · -- Side condition
    ipure_intro; exact H1
  isplit r
  · -- Side condition
    ipure_intro; exact H2
  iexact HΦ

-- NB. Keeping this code in the repo as an example for writing basic proof rules.
@[deprecated "Use dwpDesync/dwpResync instead. " (since:="2025/07/31") ]
theorem wpPureSync {Φ : Value DataT → Value DataT → @PROP DataT}
    (H1 : PureStep p1 p1') (H2 : PureStep p2 p2') (Hk : 1 ≤ K.car) :
    wp K p1' p2' Φ ⊢ wp K p1 p2 Φ := by
  -- Unfold the WP
  refine .trans ?_ (equiv_iff.mp <| wp_unfold.symm).mp
  -- Enter the right case because the programs can step
  refine .trans ?_ or_intro_r
  -- Obtain state and wp resources
  iintro Hwp σₗ σᵣ Hσ
  -- Eliminate the update (the ghost state does not need to be updated)
  apply Entails.trans _ BIUpdate.intro
  -- We will re-establish the wp for the states after one step of the left
  -- and right states, ending in (p1', σₗ) and (p2', σᵣ) respectively.
  iintro ⟨Hwp, Hs⟩
  iexists (p1', σₗ)
  iexists (p2', σᵣ)
  iexists 1
  iexists 1
  isplit r
  · -- Side condition
    ipure_intro
    simp [Hk]
    refine ⟨stepN_1_iff_step.mpr <| H1 _, stepN_1_iff_step.mpr <| H2 _⟩
  -- Eliminate the later
  refine Entails.trans ?_ Iris.BI.later_intro
  -- Conclude
  exact sep_symm

-- TODO: Port updates for heaps
theorem update_lemma (σₗ σᵣ : NML.State DataT) :
  state_interp σₗ σᵣ ⊢
    |==> (∃ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ ∗ ℓᵣ [S]⇉ᵣ∅ ∗
    state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩) :=
  sorry

-- NB. Keeping this code in the repo as an example for writing basic proof rules.
open ChipMemory in
@[deprecated "Use dwpDesync/dwpResync instead. " (since:="2025/07/31") ]
theorem wpAllocSync  {Φ : NML.Value DataT → NML.Value DataT → @PROP DataT} {K : LeibnizO Nat}
    (Hk : 1 ≤ K.car) :
     (∀ ℓₗ ℓᵣ, (ℓₗ [S]⇉ₗ∅) -∗ (ℓᵣ [S]⇉ᵣ∅) -∗ wp K (.run <| p1) (.run <| p2) Φ) ⊢
     wp K
       (.run <| ⟨.assign none (.alloc Memory.sbuf), locₗ⟩ :: p1)
       (.run <| ⟨.assign none (.alloc Memory.sbuf), loc₂⟩ :: p2)
       Φ := by
  -- Unfold the wp
  refine .trans ?_ (equiv_iff.mp <| wp_unfold.symm).mp
  -- Enter the right case because the programs can step
  refine .trans ?_ or_intro_r
  -- Obtain state and wp resources
  iintro ⟨Hrec⟩ σₗ σᵣ Hσ
  -- We must update the state to perform the allocation.
  -- Concretely, will use `update-lemma` (FIXME: rename) to do this.
  -- `update_lemma` returns resources underneath a basic update modality |==>.
  -- Because our goal also begins with a basic update modality, we are able to eliminate
  -- this modality from our updated resource using `BIUpdate.mono`.
  refine .trans (sep_mono_r <| update_lemma σₗ σᵣ) ?_
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro Hrec
  -- We will re-establish the wp for the states after the one allocation step of the left
  -- and right states.
  iexists (.run p1, ⟨freshSBUFStore σₗ.1 |>.2⟩)
  iexists (.run p2, ⟨freshSBUFStore σᵣ.1 |>.2⟩)
  iexists 1
  iexists 1
  isplit r
  · -- Side condition
    ipure_intro
    simp [Hk]
    refine ⟨?_, ?_⟩
    · exact stepN_1_iff_step.mpr (.seq <| .sbuf_alloc rfl)
    · exact stepN_1_iff_step.mpr (.seq <| .sbuf_alloc rfl)
  -- Eliminate the later
  refine .trans ?_ Iris.BI.later_intro
  -- Conclude using the updated resources and Hwp
  iintro ⟨Hwp, ℓₗ, ℓᵣ, Hℓₗ, Hℓᵣ, Hσ⟩
  ispecialize Hwp ℓₗ ℓᵣ Hℓₗ Hℓᵣ
  exact entails_preorder.refl

/-! Desynchronized WP's (dwp)

Many interesting relational proofs will take different steps on the left- and right-handed sides.
The `dwp` modality allows the left and right programs to take steps independently.
`dwp` is parameterized by four integers `Lm Rm Lx Rx`. A `dwp Lm Rm Lx Rx` allows the left program
to take between `Lm` and `Lx` steps (inclusive), likewise with the right program.

The theorem `wpDesync` introduces a `dwp` modality around a `wp k`, where the left and right
programs must take between 1 and `k` steps each (note: both programs must take at least one step).
The theorem `wpResync` eliminates a `dwp` modality, provided the minimum number of steps have been
taken on both sides.
The `dwp` modality includes a basic update, allowing for each independent step to update the state. -/

/-- The desynchronized weakest precondition modality (dwp). -/
def dwp (Lm Rm Lx Rx : Nat) (p1 p2 : ExecState DataT) (Φ : ExecState DataT → ExecState DataT → @PROP DataT) :
    @PROP DataT := iprop(
  ∀ s1, ∀ s2, state_interp s1 s2 -∗ |==>
  ∃ p1' p2', Φ p1' p2' ∗ ∃ s1' s2',
    (∃ nl nr, ⌜Lm ≤ nl ∧ Rm ≤ nr ∧ nl ≤ Lx ∧ nr ≤ Rx ∧
      SmallStep.StepN nl (p1, s1) (p1', s1') ∧ SmallStep.StepN nr (p2, s2) (p2', s2')⌝ ) ∗
    state_interp s1' s2')

/-- Introduce a `dwp` around a weakest precondition. -/
theorem wpDesync : ⊢ dwp 1 1 K.1 K.1 p1 p2 (wp K · · Φf) -∗ wp K p1 p2 Φf := by
  -- Unfold the wp and dwp
  refine .trans ?_ <| wand_mono entails_preorder.refl (equiv_iff.mp wp_unfold.symm).mp
  unfold dwp
  -- Enter the right case because the programs can step
  iintro Hdwp
  iright
  iintro sl sr Hσ
  -- Eliminate the bupd modality, gaining access to the updated resources
  ispecialize Hdwp sl sr Hσ
  refine .trans Iris.BI.emp_sep.mp (BIUpdate.mono ?_)
  iintro Hdwp
  icases Hdwp with ⟨p1', p2', Hwp, s1', s2', ⟨n1, n2, %Hstep⟩, Hupd⟩
  -- Establish wp in the updated state
  iexists (p1', s1')
  iexists (p2', s2')
  iexists n1
  iexists n2
  isplit r
  · -- Side condition
    ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, by trivial⟩ <;> try omega
  -- Eliminate the later
  refine .trans ?_ later_intro
  -- Conclude using current resources
  exact sep_symm

/-- Eliminate a `dwp` that has met its minimum step count. -/
theorem wpResync : ⊢ Φ p1 p2 -∗ dwp 0 0 Lx Rx p1 p2 Φ := by
  unfold dwp
  iintro HΦ s1 s2 Hσ
  refine .trans ?_ BIUpdate.intro
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
    refine ⟨StepN.done rfl, StepN.done rfl⟩
  · iexact Hσ

-- NB. Keeping this code in the repo as an example for writing basic proof rules.
/-- `dwp` for a single pure step on the left. -/
@[deprecated "Use dwpL with a PureStep uwp instead. " (since:="2025/07/31") ]
theorem dwpPureL (Hstep : PureStep p1 p1') (Hx : 0 < Lx := by omega) :
    ⊢ dwp (Lm - 1) Rm (Lx - 1) Rx p1' p2 Φ -∗ dwp Lm Rm Lx Rx p1 p2 Φ := by
  -- Unfold the dwp
  unfold dwp
  iintro Hdwp sl sr Hσ
  ispecialize Hdwp sl sr Hσ
  -- Eliminate the update guarding the dwp
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro Hdwp
  -- Obtain new resources from the dwp hypothesis
  icases Hdwp with ⟨p1', p2', HΦ, s1', s2', ⟨nl, nr, %Hstep⟩, Hstate⟩
  -- Reestablish dwp
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
    refine StepN.step (Hstep sl) ?_
    trivial
  · iexact Hstate


-- NB. Keeping this code in the repo as an example for writing basic proof rules.
/-- `dwp` for a single pure step on the right. -/
@[deprecated "Use dwpL with a PureStep uwp instead. " (since:="2025/07/31") ]
theorem dwpPureR (Hstep : SmallStep.PureStep p2 p2') (Hx : 0 < Rx := by omega) :
    ⊢ dwp Lm (Rm - 1) Lx (Rx - 1) p1 p2' Φ -∗ dwp Lm Rm Lx Rx p1 p2 Φ := by
  -- Unfold the dwp
  unfold dwp
  iintro Hdwp sl sr Hσ
  ispecialize Hdwp sl sr Hσ
  -- Eliminate the update guarding the dwp
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro Hdwp
  -- Obtain new resources from the dwp hypothesis
  icases Hdwp with ⟨p1', p2', HΦ, s1', s2', ⟨nl, nr, %Hstep⟩, H⟩
  -- Reestablish dwp
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
    refine StepN.step (Hstep sr) ?_
    trivial
  · iexact H

theorem update_lemma_left (σₗ σᵣ : NML.State DataT)
      (HL : ChipMemory.get_store σₗ.memory (.sbufUnboundedIndex ℓ₁) = none):
  state_interp σₗ σᵣ ⊢ |==> ((ChipMemory.freshSBUFStore σₗ.1).1 ⇉ₗ∅ ∗ state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ σᵣ) :=
  sorry

-- NB. Keeping this code in the repo as an example for writing basic proof rules.
open ChipIndex in
/-- `dwp` for a single allocation step on the left. This is a little bit simpler
than the `uwp` version since it quantifies over the generated location. -/
theorem dwpAllocL (Hx : 0 < Lx := by omega) :
    ⊢ (∀ ℓₗ, (ℓₗ [S]⇉ₗ∅) -∗
        dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| p1'.map (.bind DataT · x (.uptr <| sbufUnboundedIndex ℓₗ))) p2 Φ) -∗
      dwp Lm Rm Lx Rx (.run <| ⟨.assign (.some x) (.alloc Memory.sbuf), locₗ⟩ :: p1') p2 Φ := by
  -- Unfold the dwp in the conclusion
  iintro Hdwp
  conv => rhs; unfold dwp
  iintro sl sr Hs
  -- Update the resources
  refine .trans (sep_mono_r (update_lemma_left sl sr (ℓ₁ := sl.memory.sbufUnbounded.next_fresh) ?G)) ?_
  case G =>
    simp [ChipMemory.get_store]
    rw [← AllocHeap.get_fresh (t := sl.memory.sbufUnbounded) (H := sl.memory.sbuf_wf)]
    rfl
  iintro ⟨Hdwp, Hupd⟩
  -- Eliminate bupds from the hypotheses but not the conclusion, by duplicating the bupd in the conclusion.
  istop
  refine .trans ?_ bupd_idem.mp
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro ⟨Hdwp, ⟨Hfrac, Hauth⟩⟩
  -- Specialize Hdwp with the state alloc is stepping into
  obtain ⟨ℓ₁, Hℓ₁⟩ : ∃ ℓ₁, (ChipMemory.freshSBUFStore sl.memory).fst = .sbufUnboundedIndex ℓ₁ := by
    simp
  ispecialize Hdwp ℓ₁
  rw [Hℓ₁]
  ispecialize Hdwp Hfrac
  unfold dwp
  ispecialize Hdwp { memory := (ChipMemory.freshSBUFStore sl.memory).snd } sr Hauth
  -- Eliminate the bupd in the dwp
  -- NB. This is why we duplicated the modality before.
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  -- Obtain the updated resources
  iintro ⟨p1', p2', HΦ, s1, s2, ⟨n1, n2, %Hstep⟩, H⟩
  -- Reestablish dwp using the updated resources
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
    obtain ⟨_, _, _, _, SL, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    refine StepN.step (step.asn <| .sbuf_alloc ?_) SL
    simp at ⊢ Hℓ₁
    exact Hℓ₁.symm
  · iexact H

end weakestpre

/-- Unary weakest preconditions

We can define generic `dwp` proof rules that work whenever one side takes a step independently
of each other.
These independent steps are defined semantically, and specified using a `uwpL/uwpR` structures. -/
structure uwp (DataT : Type _) where
  pre   : PROP DataT
  post  : PROP DataT
  prog  : NML.ExecState DataT
  prog' : NML.ExecState DataT
  steps : Nat

/-- A `uwp` that uses its resources to take steps on the left. -/
structure uwpL (DataT : Type _) extends uwp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∃ σₗ', ⌜SmallStep.StepN steps (prog, σₗ) (prog', σₗ')⌝ ∗ |==> (state_interp σₗ' σᵣ ∗ post)))

/-- A `uwp` that uses its resources to take steps on the right. -/
structure uwpR (DataT : Type _) extends uwp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∃ σᵣ', ⌜SmallStep.StepN steps (prog, σᵣ) (prog', σᵣ')⌝ ∗ |==> (state_interp σₗ σᵣ' ∗ post)))

section uwp

open Iris Iris.BI Iris.BI.BIBase KLR.Core Iris NML SmallStep

variable {DataT : Type _}

/-- Step the left-hand side of a dwp using a `uwpL`. -/
theorem dwpL (u : uwpL DataT) (Hx : u.steps ≤ Lx) :
    ⊢ (u.post -∗ dwp (Lm - u.steps) Rm (Lx - u.steps) Rx u.prog' pr Φ) -∗
      u.pre -∗ dwp Lm Rm Lx Rx u.prog pr Φ := by
  -- Include the spec inside the separating context
  apply Entails.trans u.spec ?_
  -- Unfold the dwp in the conclusion
  conv => rhs; rhs; unfold dwp
  iintro Hspec Hdwp Hpre sl sr Hs
  -- Apply the spec to obtain a new post state and an update
  ispecialize Hspec sl sr Hpre Hs
  icases Hspec with ⟨sl', %Hstep, Hupd⟩
  -- Eliminate bupds from the hypotheses but not the conclusion
  istop
  refine .trans ?_ bupd_idem.mp
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro ⟨Hdwp, ⟨Hs', Hpost⟩⟩
  -- Obtain the resources from the dwp, under its bupd
  ispecialize Hdwp Hpost
  unfold dwp
  ispecialize Hdwp sl' sr Hs'
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro ⟨p1', p2', HΦ, sl'', sr'', ⟨n1, n2, %Hstep''⟩, Hs''⟩
  -- Reestablish the dwp using the new resources
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists sl''
  iexists sr''
  isplit r [Hs'']
  · iexists (n1 + u.steps)
    iexists n2
    ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep''
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    rw [Nat.add_comm _ _]
    apply StepN_add_iff.mpr
    exists (u.prog', sl')
  · iexact Hs''

/-- Step the right-hand side of a dwp using a `uwpR`. -/
theorem dwpR (u : uwpR DataT) (Hx : u.steps ≤ Rx) :
    ⊢ (u.post -∗ dwp Lm (Rm - u.steps) Lx (Rx - u.steps) pl u.prog' Φ) -∗
      u.pre -∗ dwp Lm Rm Lx Rx pl u.prog Φ := by
  -- Include the spec inside the separating context
  apply Entails.trans u.spec ?_
  -- Unfold the dwp in the conclusion
  conv => rhs; rhs; unfold dwp
  iintro Hspec Hdwp Hpre sl sr Hs
  -- Apply the spec to obtain a new post state and an update
  ispecialize Hspec sl sr Hpre Hs
  icases Hspec with ⟨sr', %Hstep, Hupd⟩
  -- Eliminate bupds from the hypotheses but not the conclusion
  istop
  refine .trans ?_ bupd_idem.mp
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro ⟨Hdwp, ⟨Hs', Hpost⟩⟩
  -- Obtain the resources from the dwp, under its bupd
  ispecialize Hdwp Hpost
  unfold dwp
  ispecialize Hdwp sl sr' Hs'
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro ⟨p1', p2', HΦ, sl'', sr'', ⟨n1, n2, %Hstep''⟩, Hs''⟩
  -- Reestablish the dwp using the new resources
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists sl''
  iexists sr''
  isplit r [Hs'']
  · iexists n1
    iexists n2 + u.steps
    ipure_intro
    obtain ⟨_, _, _, _, _, _⟩ := Hstep''
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    rw [Nat.add_comm _ _]
    apply StepN_add_iff.mpr
    exists (u.prog', sr')
  · iexact Hs''

def uwpPureL {p p' : Prog DataT} (H : PureStep p p') : uwpL DataT where
  pre   := iprop(True)
  post  := iprop(True)
  prog  := p
  prog' := p'
  steps := 1
  spec  := by
    iintro σₗ σᵣ %_ Hσ
    iexists σₗ
    isplit r
    · ipure_intro
      exact stepN_1_iff_step.mpr <| H σₗ
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

def uwpPureR {p p' : Prog DataT} (H : PureStep p p') : uwpR DataT where
  pre   := iprop(True)
  post  := iprop(True)
  prog  := p
  prog' := p'
  steps := 1
  spec  := by
    iintro σₗ σᵣ %_ Hσ
    iexists σᵣ
    isplit r
    · ipure_intro
      exact stepN_1_iff_step.mpr <| H σᵣ
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

end uwp










/-

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
-/
