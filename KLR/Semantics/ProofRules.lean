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

-- TODO: Upstream
theorem bupd_ownM_update [UCMRA M] {x y : M} : x ~~> y → UPred.ownM x ⊢ |==> UPred.ownM y := by
  intro Hupd
  refine (bupd_ownM_updateP _ (UpdateP.of_update Hupd)).trans ?_
  refine BIUpdate.mono ?_
  iintro ⟨y', %He, H⟩
  rw [He]
  iexact H

variable {DataT : Type _}

-- TODO: iapply should depricate this
theorem include_sep {P Q : @PROP DataT} (L : ⊢ P) (H : P ∗ Q ⊢ R) : Q ⊢ R := by
  refine Entails.trans ?_ (Q := iprop(P ∗ Q)) ?_
  · refine Entails.trans ?_ (Q := iprop(emp ∗ Q)) ?_
    · exact ProofMode.from_and_intro (fun n x a a => trivial) fun n x a a => a
    · exact sep_mono L fun n x a a => a
  · exact H

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
    state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩) := by
  sorry

-- NB. Keeping this code in the repo as an example for writing basic proof rules.
open ChipMemory in
@[deprecated "Use dwpDesync/dwpResync instead. " (since:="2025/07/31") ]
theorem wpAllocSync  {Φ : NML.Value DataT → NML.Value DataT → @PROP DataT} {K : LeibnizO Nat}
    (Hk : 2 ≤ K.car) :
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
  iexists 2
  iexists 2
  isplit r
  · -- Side condition
    ipure_intro
    simp only [Nat.zero_lt_succ, Hk, _root_.true_and]
    have Htwo : 1 + 1 = 2 := by rfl
    rw [← Htwo, StepN_add_iff, StepN_add_iff]
    refine ⟨?_, ?_⟩
    · exists (ExecState.run ({ stmt := NML.Stmt.assign none (.val (.uptr (ChipMemory.freshSBUFStore σₗ.memory).1)), env := locₗ } :: p1), State.mk (ChipMemory.freshSBUFStore σₗ.memory).2)
      refine ⟨?_, ?_⟩
      · refine stepN_1_iff_step.mpr ?_
        apply LiftEAsn
        exact ExprStep.sbuf_alloc rfl
      · exact stepN_1_iff_step.mpr step.seqV
    · exists (ExecState.run ({ stmt := NML.Stmt.assign none (.val (.uptr (ChipMemory.freshSBUFStore σᵣ.memory).1)), env := loc₂ } :: p2), State.mk (ChipMemory.freshSBUFStore σᵣ.memory).2)
      refine ⟨?_, ?_⟩
      · refine stepN_1_iff_step.mpr ?_
        apply LiftEAsn
        exact ExprStep.sbuf_alloc rfl
      · exact stepN_1_iff_step.mpr step.seqV
  -- Eliminate the later
  refine .trans ?_ Iris.BI.later_intro
  -- Conclude using the updated resources and Hwp
  iintro ⟨Hwp, ℓₗ, ℓᵣ, Hℓₗ, Hℓᵣ, Hσ⟩
  ispecialize Hwp ℓₗ ℓᵣ Hℓₗ Hℓᵣ
  isplit l [Hσ]
  · iapply Hσ
  · iapply Hwp

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

theorem update_lemma_left (σₗ σᵣ : NML.State DataT) (HL : ChipMemory.get_store σₗ.memory (.sbufUnboundedIndex ℓ₁) = none):
  state_interp σₗ σᵣ ⊢ |==> ((ChipMemory.freshSBUFStore σₗ.1).1 ⇉ₗ∅ ∗ state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ σᵣ) := by
  unfold state_interp
  unfold heProp_auth
  unfold PointsToS
  unfold heProp_frag
  simp only []
  -- Combine the ownM into an op
  refine .trans ?_ (BIUpdate.mono BI.sep_comm.mp)
  refine .trans ?_ (BIUpdate.mono ((UPred.ownM_op _ _).mp))
  apply bupd_ownM_update
  have X := @heap_view_alloc PNat ProdNeuronIndex (Agree (LeibnizO DataT)) ProdNeuronMemory _ _ _
    (hhmap (fun x v => some (toAgree ( LeibnizO.mk v ))) ( ProdStore.mk σₗ.memory σᵣ.memory ))
    -- Ah, this is updating an infinite number of cells so needs special treatment
    -- (.left (ChipMemory.freshSBUFStore σₗ.memory).snd)

    -- Maybe what we need is for the state_interp to also include frag ownership for
    -- all spaces after the allocated part.
  sorry

theorem update_lemma_right (σₗ σᵣ : NML.State DataT)
      (HL : ChipMemory.get_store σᵣ.memory (.sbufUnboundedIndex ℓ₂) = none):
  state_interp σₗ σᵣ ⊢ |==> ((ChipMemory.freshSBUFStore σᵣ.1).1 ⇉ₗ∅ ∗ state_interp σₗ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩) :=
  sorry






-- NB. Keeping this code in the repo as an example for writing basic proof rules.
open ChipIndex in
/-- `dwp` for a single allocation step on the left. This is a little bit simpler
than the `uwp` version since it quantifies over the generated location. -/
theorem dwpAllocL (Hx : 1 < Lx := by omega) :
    ⊢ (∀ ℓₗ, (ℓₗ [S]⇉ₗ∅) -∗
        dwp (Lm - 2) Rm (Lx - 2) Rx (.run <| p1'.map (.bind DataT · x (.uptr <| sbufUnboundedIndex ℓₗ))) p2 Φ) -∗
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
  · iexists (n1 + 2)
    iexists n2
    ipure_intro
    obtain ⟨_, _, _, _, SL, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    have Htwo : 1 + 1 = 2 := by rfl
    rw [Nat.add_comm _ _, ← Htwo, Nat.add_assoc, StepN_add_iff]
    rename_i pi _ _ _ _ _
    exists (ExecState.run ({ stmt := NML.Stmt.assign (some x) (.val (.uptr (ChipMemory.freshSBUFStore sl.memory).1)), env := locₗ } :: pi), State.mk (ChipMemory.freshSBUFStore sl.memory).2)
    refine ⟨?_, ?_⟩
    · exact stepN_1_iff_step.mpr <| .asnE <| .sbuf_alloc rfl
    rw [StepN_add_iff]
    exists (ExecState.run (List.map (fun x_1 => NML.Task.bind DataT x_1 x (Value.uptr (sbufUnboundedIndex ℓ₁))) pi), { memory := (ChipMemory.freshSBUFStore sl.memory).snd })
    refine ⟨?_, SL⟩
    apply stepN_1_iff_step.mpr
    rw [Hℓ₁]
    exact step.asnV
  · iexact H


open ChipIndex in
theorem dwpAllocR (Hx : 1 < Rx := by omega) :
    ⊢ (∀ ℓᵣ, (ℓᵣ [S]⇉ₗ∅) -∗
        dwp Lm (Rm - 2) Lx (Rx - 2) p1 (.run <| p2'.map (.bind DataT · x (.uptr <| sbufUnboundedIndex ℓᵣ))) Φ) -∗
      dwp Lm Rm Lx Rx p1 (.run <| ⟨.assign (.some x) (.alloc Memory.sbuf), locₗ⟩ :: p2') Φ := by
  -- Unfold the dwp in the conclusion
  iintro Hdwp
  conv => rhs; unfold dwp
  iintro sl sr Hs
  -- Update the resources
  refine .trans (sep_mono_r (update_lemma_right sl sr (ℓ₂ := sr.memory.sbufUnbounded.next_fresh) ?G)) ?_
  case G =>
    simp [ChipMemory.get_store]
    rw [← AllocHeap.get_fresh (t := sr.memory.sbufUnbounded) (H := sr.memory.sbuf_wf)]
    rfl
  iintro ⟨Hdwp, Hupd⟩
  -- Eliminate bupds from the hypotheses but not the conclusion, by duplicating the bupd in the conclusion.
  istop
  refine .trans ?_ bupd_idem.mp
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro ⟨Hdwp, ⟨Hfrac, Hauth⟩⟩
  -- Specialize Hdwp with the state alloc is stepping into
  obtain ⟨ℓ₂, Hℓ₂⟩ : ∃ ℓ₂, (ChipMemory.freshSBUFStore sr.memory).fst = .sbufUnboundedIndex ℓ₂ := by
    simp
  ispecialize Hdwp ℓ₂
  rw [Hℓ₂]
  ispecialize Hdwp Hfrac
  unfold dwp
  ispecialize Hdwp sl { memory := (ChipMemory.freshSBUFStore sr.memory).snd } Hauth
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
  · iexists n1
    iexists (n2 + 2)
    ipure_intro
    obtain ⟨_, _, _, _, _, SR⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    have Htwo : 1 + 1 = 2 := by rfl
    rw [Nat.add_comm _ _, ← Htwo, Nat.add_assoc, StepN_add_iff]
    rename_i pi _ _ _ _ _
    exists (ExecState.run ({ stmt := NML.Stmt.assign (some x) (.val (.uptr (ChipMemory.freshSBUFStore sr.memory).1)), env := locₗ } :: pi), State.mk (ChipMemory.freshSBUFStore sr.memory).2)
    refine ⟨?_, ?_⟩
    · apply stepN_1_iff_step.mpr  ?_
      apply step.asnE
      apply ExprStep.sbuf_alloc
      rfl
    · rw [StepN_add_iff]
      exists (ExecState.run (List.map (fun x_1 => NML.Task.bind DataT x_1 x (Value.uptr (sbufUnboundedIndex ℓ₂))) pi), { memory := (ChipMemory.freshSBUFStore sr.memory).snd })
      refine ⟨?_, ?_⟩
      · apply stepN_1_iff_step.mpr
        rw [Hℓ₂]
        exact step.asnV
      · exact SR
  · iexact H

theorem update_set_lemma_left (σₗ σᵣ : NML.State DataT) (mv mv' : Option DataT) :
  ⊢ (ℓ ↦ₗ mv) -∗ state_interp σₗ σᵣ -∗
    |==> ((ℓ ↦ₗ mv') ∗ state_interp { σₗ with memory := Store.set σₗ.memory ℓ mv' } σᵣ) := by
  unfold state_interp
  unfold heProp_auth
  unfold PointsTo
  unfold heProp_frag
  simp only []
  -- -- Combine the ownM into an op
  -- refine .trans ?_ (BIUpdate.mono BI.sep_comm.mp)
  -- refine .trans ?_ (BIUpdate.mono ((UPred.ownM_op _ _).mp))
  -- apply bupd_ownM_update
  -- have X := @heap_view_alloc PNat ProdNeuronIndex (Agree (LeibnizO DataT)) ProdNeuronMemory _ _ _
  --   (hhmap (fun x v => some (toAgree ( LeibnizO.mk v ))) ( ProdStore.mk σₗ.memory σᵣ.memory ))
  --   -- (.left (ChipMemory.freshSBUFStore σₗ.memory).snd)
  sorry

theorem update_set_lemma_right (σₗ σᵣ : NML.State DataT) (mv mv' : Option DataT) :
  ⊢ (ℓ ↦ᵣ mv) -∗ state_interp σₗ σᵣ -∗
    |==> ((ℓ ↦ᵣ mv') ∗ state_interp σₗ { σᵣ with memory := Store.set σᵣ.memory ℓ mv' } ) :=
  sorry


theorem dwpSetpL {v : DataT} (Hx : 0 < Lx := by omega) :
    ⊢ ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| p1) p2 Φ) -∗
       (⟨i, x⟩ ↦ₗ mv) -∗
       (dwp Lm Rm Lx Rx (.run <| ⟨.set_point (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v), loc⟩ :: p1) p2 Φ) := by
  -- Unfold the dwp in the conclusion
  iintro Hdwp
  conv => rhs; unfold dwp
  iintro Hmv sl sr Hs
  -- Add the update lemma to the context
  refine include_sep (@update_set_lemma_left DataT ⟨i, x⟩ sl sr mv (some v)) ?_
  iintro ⟨Hupd, ⟨Hdwp, Hmv⟩, Hσ⟩
  ispecialize Hupd Hmv Hσ
  -- Eliminate bupds from the hypotheses but not the conclusion, by duplicating the bupd in the conclusion.
  istop
  refine .trans ?_ bupd_idem.mp
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro ⟨Hdwp, ⟨Hfrac, Hauth⟩⟩
  -- Specialize, unfold, and specialize the dwp
  ispecialize Hdwp Hfrac
  unfold dwp
  ispecialize Hdwp _ sr Hauth
  -- Eliminate the bupd
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  -- Conclude using the current hypotheses
  iintro ⟨p1', p2', HΦ, s1, s2, ⟨n1, n2, %Hstep⟩, H⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists s1
  iexists s2
  isplit r [H] <;> try iexact H
  iexists (n1 + 1)
  iexists n2
  ipure_intro
  obtain ⟨_, _, _, _, SL, _⟩ := Hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
  rw [Nat.add_comm _ _, StepN_add_iff]
  refine ⟨_, ⟨stepN_1_iff_step.mpr step.setp, SL⟩⟩

theorem dwpSetpR {v : DataT} (Hx : 0 < Rx := by omega) :
    ⊢ ((⟨i, x⟩ ↦ᵣ some v) -∗ dwp Lm (Rm - 1) Lx (Rx - 1) p1 (.run <| p2) Φ) -∗
       (⟨i, x⟩ ↦ᵣ mv) -∗
       (dwp Lm Rm Lx Rx p1 (.run <| ⟨.set_point (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v), loc⟩ :: p2) Φ) := by
  -- Unfold the dwp in the conclusion
  iintro Hdwp
  conv => rhs; unfold dwp
  iintro Hmv sl sr Hs
  -- Add the update lemma to the context
  refine include_sep (@update_set_lemma_right DataT ⟨i, x⟩ sl sr mv (some v)) ?_
  iintro ⟨Hupd, ⟨Hdwp, Hmv⟩, Hσ⟩
  ispecialize Hupd Hmv Hσ
  -- Eliminate bupds from the hypotheses but not the conclusion, by duplicating the bupd in the conclusion.
  istop
  refine .trans ?_ bupd_idem.mp
  refine .trans bupd_frame_l (BIUpdate.mono ?_)
  iintro ⟨Hdwp, ⟨Hfrac, Hauth⟩⟩
  -- Specialize, unfold, and specialize the dwp
  ispecialize Hdwp Hfrac
  unfold dwp
  ispecialize Hdwp sl _ Hauth
  -- Eliminate the bupd
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  -- Conclude using the current hypotheses
  iintro ⟨p1', p2', HΦ, s1, s2, ⟨n1, n2, %Hstep⟩, H⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists s1
  iexists s2
  isplit r [H] <;> try iexact H
  iexists n1
  iexists (n2 + 1)
  ipure_intro
  obtain ⟨_, _, _, _, _, SR⟩ := Hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
  rw [Nat.add_comm _ _, StepN_add_iff]
  refine ⟨_, ⟨stepN_1_iff_step.mpr step.setp, SR⟩⟩

-- TODO: This is only used for an example right now, a less ad-hoc solution for
-- ExprSteps that use state is necessary.
theorem dwpReadpRetL {v : DataT} (Hx : 0 < Lx := by omega) :
    ⊢ ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| ⟨.ret (.val <| .data v), loc⟩ :: p1) p2 Φ) -∗
      (⟨i, x⟩ ↦ₗ some v) -∗
      (dwp Lm Rm Lx Rx (.run <| ⟨.ret <| .read_point (.val <| .uptr i) (.val <| .iptr x), loc⟩ :: p1) p2 Φ) := by
  iintro Hdwp Hfrag
  conv => rhs; unfold dwp
  iintro sl sr Hs
  -- Use one of the validity lemmas to get...
  istop
  have Hstore : Store.get sl.memory (⟨i, x⟩ : ChipCellIndex) = some v := sorry
  istart
  iintro ⟨⟨Hdwp, Hfrag⟩, Hs⟩
  unfold dwp
  ispecialize Hdwp Hfrag _ _ Hs
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro ⟨p1', p2', HΦ, s1, s2, ⟨n1, n2, %Hstep⟩, H⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists s1
  iexists s2
  isplit r [H] <;> try iexact H
  iexists (n1 + 1)
  iexists n2
  ipure_intro
  obtain ⟨_, _, _, _, SL, _⟩ := Hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
  rw [Nat.add_comm _ _, StepN_add_iff]
  refine ⟨_, ⟨stepN_1_iff_step.mpr ?_, SL⟩⟩
  apply NML.step.retE
  exact ExprStep.readp Hstore


theorem dwpReadpRetL' {v : DataT} (Hx : 0 < Lx := by omega) :
    ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| ⟨.ret (.val <| .data v), loc⟩ :: p1) p2 Φ) ∗
      (⟨i, x⟩ ↦ₗ some v) ⊢
      (dwp Lm Rm Lx Rx (.run <| ⟨.ret <| .read_point (.val <| .uptr i) (.val <| .iptr x), loc⟩ :: p1) p2 Φ) := by
  apply BI.wand_entails
  apply Entails.trans (dwpReadpRetL (v := v))
  istart
  iintro H1 ⟨H2, H3⟩
  iapply H1 with [H2]
  · iexact H2
  · iexact H3

/-- Proof rule for a completed loop on the left -/
theorem dwpLoopDoneL (Hx : 1 < Lx := by omega) :
    ⊢ dwp (Lm - 1) Rm (Lx - 1) Rx (.run p1') p2 Φ -∗
      dwp Lm Rm Lx Rx (.run <| (⟨NML.Stmt.loop AffineIter s .none body, loc⟩ :: p1')) p2 Φ := by
  iintro Hdwp
  unfold dwp
  iintro sl sr Hs
  ispecialize Hdwp sl sr Hs
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro ⟨p1', p2', HΦ, sl', sr', ⟨nl, nr, %Hstep⟩, Hσ⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists sl'
  iexists sr'
  isplit r [Hσ]
  · iexists (nl + 1)
    iexists nr
    ipure_intro
    obtain ⟨_, _, _, _, SL, _⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    rw [Nat.add_comm, StepN_add_iff]
    refine ⟨_, ?_, SL⟩
    refine stepN_1_iff_step.mpr ?_
    exact step.loop_exit
  · iexact Hσ

/-- Proof rule for a completed loop on the left -/
theorem dwpLoopDoneR (Hx : 1 < Rx := by omega) :
    ⊢ dwp Lm (Rm - 1) Lx (Rx - 1) p1 (.run p2') Φ -∗
      dwp Lm Rm Lx Rx p1 (.run <| (⟨NML.Stmt.loop AffineIter s .none body, loc⟩ :: p2')) Φ := by
  iintro Hdwp
  unfold dwp
  iintro sl sr Hs
  ispecialize Hdwp sl sr Hs
  refine .trans emp_sep.mp (BIUpdate.mono ?_)
  iintro ⟨p1', p2', HΦ, sl', sr', ⟨nl, nr, %Hstep⟩, Hσ⟩
  iexists p1'
  iexists p2'
  isplit l [HΦ]
  · iexact HΦ
  iexists sl'
  iexists sr'
  isplit r [Hσ]
  · iexists nl
    iexists nr + 1
    ipure_intro
    obtain ⟨_, _, _, _, _, SR⟩ := Hstep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
    rw [Nat.add_comm, StepN_add_iff]
    refine ⟨_, ?_, SR⟩
    refine stepN_1_iff_step.mpr ?_
    exact step.loop_exit
  · iexact Hσ



-- /- Proposition over locals. Used for generalization.
-- LocProp should be solvable by `simp` for good automation. -/
-- def LocProp (DataT : Type _) := @NML.Locals DataT → Prop
-- @[simp] nonrec def LocProp.True : LocProp DataT := fun _ => True
-- @[simp] def LocProp.And (p1 p2 : LocProp DataT) : LocProp DataT := fun loc => p1 loc ∧ p2 loc
-- @[simp] def LocProp.Inc (s : String) (v : @Value DataT) : LocProp DataT := fun loc => loc s = some v
-- @[simp] def LocProp.Emp (s : String) : LocProp DataT := fun loc => loc s = none


/-- Generalize a wp by a relationship on its locations -/
theorem wp_gen_loc (R : Locals DataT → Locals DataT → Prop) :
  ⊢ (∀ locₗ locᵣ, ⌜R locₗ locᵣ⌝ -∗ wp (DataT := DataT) K (.run <| ⟨sₗ, locₗ⟩ :: pₗ) (.run <| ⟨sᵣ, locᵣ⟩ :: pᵣ) Φ) -∗
    ⌜R llₗ llᵣ⌝ -∗
    wp (DataT := DataT) K (.run <| ⟨sₗ, llₗ⟩ :: pₗ) (.run <| ⟨sᵣ, llᵣ⟩ :: pᵣ) Φ := by
  iintro H HR
  ispecialize H _ _ HR
  iexact H







end weakestpre












/-- Unary weakest preconditions

We can define generic `dwp` proof rules that work whenever one side takes a step independently
of each other.
These independent steps are defined semantically, and specified using a `uwpL/uwpR` structures.

TODO: At the moment, allocL/R cannot be implemented as a UWP because the prog' and post cannot
depend on state. Should this be fixed? I think it pretty much only matters in that case because
the output has a state that is not mentioned by the input.


TODO: Not sure this actually works at the frontend. Maybe make it a typeclass?
-/
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
    ⊢ u.pre ∗ (u.post -∗ dwp (Lm - u.steps) Rm (Lx - u.steps) Rx u.prog' pr Φ)  -∗
      dwp Lm Rm Lx Rx u.prog pr Φ := by
  -- Include the spec inside the separating context
  apply Entails.trans u.spec ?_
  -- Unfold the dwp in the conclusion
  conv => rhs; rhs; unfold dwp
  iintro Hspec ⟨Hpre, Hdwp⟩ sl sr Hs
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

-- Let's see if this even works before going ham with the refactoring
theorem dwpL' (u : uwpL DataT) (Hx : u.steps ≤ Lx) :
    u.pre ∗ (u.post -∗ dwp (Lm - u.steps) Rm (Lx - u.steps) Rx u.prog' pr Φ) ⊢
    dwp Lm Rm Lx Rx u.prog pr Φ := (wand_entails <| dwpL u Hx)

/-- Step the right-hand side of a dwp using a `uwpR`. -/
theorem dwpR (u : uwpR DataT) (Hx : u.steps ≤ Rx) :
    ⊢ u.pre ∗ (u.post -∗ dwp Lm (Rm - u.steps) Lx (Rx - u.steps) pl u.prog' Φ) -∗
      dwp Lm Rm Lx Rx pl u.prog Φ := by
  -- Include the spec inside the separating context
  apply Entails.trans u.spec ?_
  -- Unfold the dwp in the conclusion
  conv => rhs; rhs; unfold dwp
  iintro Hspec ⟨Hpre, Hdwp⟩ sl sr Hs
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

-- Let's see if this even works before going ham with the refactoring
theorem dwpR' (u : uwpR DataT) (Hx : u.steps ≤ Rx) :
    u.pre ∗ (u.post -∗ dwp Lm (Rm - u.steps) Lx (Rx - u.steps) pl u.prog' Φ)
    ⊢ dwp Lm Rm Lx Rx pl u.prog Φ :=
  (wand_entails <| dwpR u Hx)

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

-- | load_full :
--     AffineMap.is_trivial asn →
--     ExprStep e loc st (.ptr tensor) st' →
--     -- The source tensor must have index in HBM (can be generalized), and be allocated
--     tensor.index = ChipIndex.hbmIndex src_index →
--     ChipMemory.get_store st'.memory tensor.index = some src_store →
--     -- The destination tensor is a fresh tensor in SBUF, with updated state.
--     ⟨dst_index, memory''⟩ = ChipMemory.freshSBUFStore st'.memory →
--     ExprStep (.load asn e) loc st
--       -- Return value: The input tensor, but with its chip index updated to be the fresh tensor.
--       -- All other metadata is the same.
--       (.ptr {tensor with index := dst_index })
--       -- Return state: Update the SBUF state at the fresh index to contain the source store.
--       (State.mk <| ChipMemory.set_store memory'' dst_index (some src_store))


-- Next up:
-- Desync'd Moving tensors (load_full)
-- Sync'd Control flow (iterators as values)
-- Desync'd tensorscalar
-- Sync'd ret_assert
-- This should be enought to verify loop fusion



end uwp

section ewp

open Iris Iris.BI Iris.BI.BIBase KLR.Core Iris NML SmallStep

-- Like UWP but for ExprStep
structure ewp (DataT : Type _) where
  pre   : PROP DataT
  post  : PROP DataT
  expr  : NML.Expr DataT
  -- Using a predicate on locations instead of a single location becase
  -- we do not have separating conjunction over them.
  locP  : NML.Locals DataT → Prop
  expr' : NML.Expr DataT

/-- An `ewp` that uses its resources to take steps on the left. -/
structure ewpL (DataT : Type _) extends ewp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∀ loc, ∃ σₗ', ⌜locP loc → ExprStep DataT expr loc σₗ expr' σₗ'⌝ ∗ |==> (state_interp σₗ' σᵣ ∗ post)))

/-- An `ewp` that uses its resources to take steps on the left. -/
structure ewpR (DataT : Type _) extends ewp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∀ loc, ∃ σᵣ', ⌜locP loc → ExprStep DataT expr loc σᵣ expr' σᵣ'⌝ ∗ |==> (state_interp σₗ σᵣ' ∗ post)))

def liftE (e : ewp DataT) (p : Expr DataT → Stmt DataT) (ps : List (NML.Task DataT)) (loc : NML.Locals DataT) : uwp DataT where
  pre   := e.pre
  post  := e.post
  prog  := .run <| ⟨p e.expr,  loc⟩ :: ps
  prog' := .run <| ⟨p e.expr', loc⟩ :: ps
  steps := 1

/-- Lift an `ewpL` to a `uwpL` provided the context is `ExprLift` -/
def liftEL (e : ewpL DataT) {p : Expr DataT → Stmt DataT} (Hp : ExprLift p) {ps : List (NML.Task DataT)}
     {loc : NML.Locals DataT} (Hloc : e.locP loc) : uwpL DataT where
  touwp := liftE e.toewp p ps loc
  spec  := by
    apply Entails.trans e.spec ?_
    simp only [liftE]
    iintro Hspec σₗ σᵣ Hpre Hσ
    ispecialize Hspec σₗ σᵣ Hpre Hσ loc
    icases Hspec with ⟨Hσₗ', %Hstep, Hupd⟩
    iexists Hσₗ'
    isplit r
    · ipure_intro
      exact stepN_1_iff_step.mpr (Hp e.expr e.expr' σₗ Hσₗ' loc ps (Hstep Hloc))
    · iexact Hupd

/-- Lift an `ewpR` to a `uwpR` provided the context is `ExprLift` -/
def liftER (e : ewpR DataT) {p : Expr DataT → Stmt DataT} (Hp : ExprLift p) {ps : List (NML.Task DataT)}
    {loc : NML.Locals DataT} (Hloc : e.locP loc) : uwpR DataT where
  touwp := liftE e.toewp p ps loc
  spec  := by
    apply Entails.trans e.spec ?_
    simp only [liftE]
    iintro Hspec σₗ σᵣ Hpre Hσ
    ispecialize Hspec σₗ σᵣ Hpre Hσ loc
    icases Hspec with ⟨Hσᵣ', %Hstep, Hupd⟩
    iexists Hσᵣ'
    isplit r
    · ipure_intro
      exact stepN_1_iff_step.mpr (Hp e.expr e.expr' σᵣ Hσᵣ' loc ps (Hstep Hloc))
    · iexact Hupd

def ewpVarL (s : String) (v : Value DataT) : ewpL DataT where
  pre   := iprop(True)
  post  := iprop(True)
  expr  := .var s
  locP  := (· s = some v)
  expr' := .val v
  spec  := by
    iintro σₗ σᵣ %_ Hσ loc
    iexists σₗ
    isplit r
    · ipure_intro
      exact ExprStep.var
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

def ewpVarR (s : String) (v : Value DataT) : ewpR DataT where
  pre   := iprop(True)
  post  := iprop(True)
  expr  := .var s
  locP  := (· s = some v)
  expr' := .val v
  spec  := by
    iintro σₗ σᵣ %_ Hσ loc
    iexists σᵣ
    isplit r
    · ipure_intro
      exact ExprStep.var
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

-- NTS: Not sure I want to do sbuf_alloc in this format because the expression returned it depends on state
-- But you should add set or something to make sure it works


end ewp




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
