/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Logic
import KLR.Semantics.SmallStep

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



section algebra

/-! Update lemmas (WIP)

To modify ghost state (terms in the separation logic like `l ⇉ₗ∅` or `⟨c, x⟩ ↦ v`, which desugar to
`UPred.ownM` terms), Iris uses the |==> modality. Specifically, the lemma `bupd_ownM_update` says that
```
x ~~> y → UPred.ownM x ⊢ |==> UPred.ownM y
```
In other words, if there is a `x ~~> y` update proven in the Iris libray, we are allowed to update
an `UPred.ownM x` resource to an `UPred.ownM y`  resource, under an "update modality" `|==>`.
The important updates for us are in `src/Iris/Algebra/HeapView.lean`.

In this section, I prove the update lemmas we need for all of the proof rules. -/


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

-- TODO: Port updates for heaps
theorem update_lemma (σₗ σᵣ : NML.State DataT) :
  state_interp σₗ σᵣ ⊢
    |==> (∃ ℓₗ ℓᵣ, ℓₗ [S]⇉ₗ∅ ∗ ℓᵣ [S]⇉ᵣ∅ ∗
    state_interp ⟨(ChipMemory.freshSBUFStore σₗ.1).2⟩ ⟨(ChipMemory.freshSBUFStore σᵣ.1).2⟩) := by
  sorry

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


end algebra


section basicrules

/-! Basic proof rules

The most basic proof rules. For these, both programs must take at least one step.
-/


variable [NMLEnv DataT]

/-- Two values are related when they are related by Φ. -/
theorem wpValVal (H1 : toVal p1 = some v1) (H2 : toVal p2 = some v2) :
    Φ v1 v2 ⊢ wp (DataT := DataT) K p1 p2 Φ := by
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
    (H1 : PureStep p1 p1') (H2 : PureStep p2 p2') (Hk : 1 ≤ K) :
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
  refine Entails.trans ?_ BIUpdate.intro
  -- Conclude
  exact sep_symm

-- TODO: The "free" BiLoeb instance from BILaterContractive (which we have done for UPred)
instance : BILoeb (PROP DataT) := sorry

theorem wpMono' {Φ : Value DataT → Value DataT → @PROP DataT} (P : PROP DataT) :
    ⊢ ∀ p1 p2, P ∗ wp k p1 p2 Φ -∗ wp k p1 p2 (iprop(Φ · · ∗ P)) := by
  refine BI.wand_entails (Entails.trans ?_ loeb)
  istart
  iintro IH - p1 p2  ⟨HP, Hwp⟩
  refine .trans (sep_mono .rfl (equiv_iff.mp <| wp_unfold).mp) ?_
  refine .trans ?_ (equiv_iff.mp <| wp_unfold).mpr
  iintro ⟨p, (Hwp | Hwp)⟩
  · ileft
    refine .trans bupd_frame_l (BIUpdate.mono ?_)
    iintro ⟨⟨-, P⟩, ⟨vl, vr, %H1, %H2, HΦ⟩⟩
    iexists vl
    iexists vr
    isplit r; ipure_intro; trivial
    isplit r; ipure_intro; trivial
    isplit l [HΦ]
    · iexact HΦ
    · iexact P
  · iright
    iintro sl sr Hσ
    ispecialize Hwp sl sr Hσ
    refine .trans bupd_frame_l (BIUpdate.mono ?_)
    iintro ⟨⟨IH, P⟩, cl', cr', nl, nr, %Hpure, Hwp⟩
    iexists cl'
    iexists cr'
    iexists nl
    iexists nr
    isplit r; ipure_intro; trivial
    -- Eliminate the later
    istop
    refine .trans (sep_mono (sep_mono .rfl later_intro) .rfl) ?_
    refine .trans (sep_mono later_sep.mpr .rfl) ?_
    refine .trans later_sep.mpr ?_
    refine later_mono ?_
    -- Eliminate the bupd
    refine .trans bupd_frame_l ?_
    refine BIUpdate.mono ?_
    -- Hack: add in a .emp term to specialize the IH
    refine .trans sep_emp.mpr ?_
    istart
    iintro ⟨⟨⟨IH, HP⟩, ⟨Hσ, Hwp⟩⟩, Hemp⟩
    isplit l [Hσ]; iexact Hσ
    ispecialize IH Hemp cl'.fst cr'.fst
    iapply IH
    isplit l [HP]; iexact HP
    iexact Hwp

theorem wpMono {Φ : Value DataT → Value DataT → @PROP DataT} (P : PROP DataT) :
    P ∗ wp k p1 p2 Φ ⊢ wp k p1 p2 (iprop(Φ · · ∗ P)) := by
  sorry

theorem wpMonoPost {P Q : Value DataT → Value DataT → @PROP DataT} :
    (∀ vl vr, P vl vr -∗ Q vl vr) ∗ (wp k p1 p2 P) ⊢ wp k p1 p2 Q := by
  sorry

/-
theorem wpFrameSync' {Φ : Value DataT → Value DataT → PROP DataT} (Hk : 1 ≤ k):
    ⊢ ∀ piL piR,
        ⌜NML.SimpleStackFrame piL ∧ NML.SimpleStackFrame piR⌝ ∗
        wp k ⟨.run piL, []⟩ ⟨.run piR, []⟩
          (fun v1 v2 => iprop(⌜v1 = .kont⌝ ∗ ⌜v2 = .kont⌝ ∗ wp k ⟨.run poL, Fl⟩ ⟨.run poR, Fr⟩ Φ))
    -∗ wp k ⟨.run piL, poL :: Fl⟩ ⟨.run piR, poR :: Fr⟩ Φ := by
  refine BI.wand_entails (Entails.trans ?_ loeb)
  istart
  iintro IH - piL piR Hwp
  -- Unfold the wp in the hypothesis
  refine .trans (sep_mono .rfl (sep_mono .rfl (equiv_iff.mp <| wp_unfold).mp)) ?_
  -- Unfold the wp in the conclusion
  refine .trans ?_ (equiv_iff.mp <| wp_unfold).mpr
  istart
  iintro ⟨IH, %Hsimple, (H|H)⟩
  · -- Value case.
    -- Still use right case to take exactly one step to move to the continuation
    -- Apply the wp
    iright
    iintro sl sr Hσ
    -- Clear the bupds
    istop
    apply Entails.trans sep_assoc.mp ?_
    apply Entails.trans (sep_mono .rfl BIUpdate.frame_r) ?_
    apply Entails.trans bupd_frame_l ?_
    apply BIUpdate.mono
    istart

    -- Obtain new resources
    iintro ⟨-, ⟨vk1, vk2, %Hv1, %Hv2, %Hvk1, %Hvk2, Hwp⟩, Hσ⟩

    -- It will step to the continuation in one step
    iexists ⟨⟨ExecState.run poL, Fl⟩, sl⟩
    iexists ⟨⟨ExecState.run poR, Fr⟩, sr⟩
    iexists 1
    iexists 1
    isplit r
    · ipure_intro
      -- A run state being value implies that b1 and b2 are both empty
      cases piL
      cases piR
      obtain ⟨_, rfl⟩ := NML.toVal_run_isSome_inv _ Hv1
      obtain ⟨_, rfl⟩ := NML.toVal_run_isSome_inv _ Hv2
      refine ⟨Nat.one_pos, Nat.one_pos, Hk, Hk, ?_, ?_⟩
      · apply stepN_1_iff_step.mpr rfl
      · exact stepN_1_iff_step.mpr rfl
    istop
    -- Turn the crank
    refine .trans ?_ later_intro
    refine .trans ?_ BIUpdate.intro
    istart
    iintro ⟨Hwp, Hσ⟩
    isplit l [Hσ]
    · iexact Hσ
    · iexact Hwp
  · -- Lift the steps from the wp up into the frame
    iright
    iintro sl sr Hσ
    ispecialize H sl sr Hσ

    -- We will have to update the resources so only clear the bupd from the hypothesis
    istop
    apply Entails.trans bupd_frame_l ?_
    apply BIUpdate.mono
    istart
    iintro ⟨IH, ⟨cl', cr', nl, nr, %Hsteps, H⟩⟩
    obtain ⟨Hnl, Hnr, Hnlx, Hnrx, HstepL, HstepR⟩ := Hsteps

    -- cl' and cr' are both .run .. []
    obtain ⟨PiL', sl', rfl⟩ := StepN_run_noframe_inv Hsimple.1 HstepL
    obtain ⟨PiR', sr', rfl⟩ := StepN_run_noframe_inv Hsimple.2 HstepR
    simp only []

    -- -- rcases Hsteps with ⟨Hnl, Hnr, Hnlx, Hnrx, Hsl, Hsr⟩
    -- Will step to cl' and cr'
    iexists (⟨ExecState.run PiL', poL :: Fl⟩, sl')
    iexists (⟨ExecState.run PiR', poR :: Fr⟩, sr')
    iexists nl
    iexists nr
    isplit r
    · ipure_intro
      -- Step lifting lemma: If we can make steps in an empty context
      -- The same steps in an extended context will also reach the same state.
      refine ⟨Hnl, Hnr, Hnlx, Hnrx, ?_, ?_⟩
      · exact StepN_run_noframe_lift HstepL
      · exact StepN_run_noframe_lift HstepR
    -- Get the resources out from under the later
    apply Entails.trans later_sep.mpr
    apply later_mono

    -- Hack: specialize the emp from the IH
    refine .trans sep_emp.mpr ?_
    istart
    iintro ⟨⟨IH, Hwp⟩, Hemp⟩
    ispecialize IH Hemp PiL' PiR'

    -- Eliminate the bupd
    refine .trans BIUpdate.frame_r ?_
    refine BIUpdate.mono ?_
    istart
    iintro ⟨⟨Hσ, IH⟩, Hwp⟩
    isplit l [Hσ]
    · iexact Hσ
    simp
    iapply Hwp
    isplit r
    · ipure_intro
      -- TODO: Prove that executing inside a simple frame leaves a simple frame
      sorry
    iexact IH
-/

/-
theorem wpFrameSync {Φ : Value DataT → Value DataT → PROP DataT} (Hk : 1 ≤ k)
    (HSL : NML.SimpleStackFrame piL) (HSR : NML.SimpleStackFrame piR) :
    wp k ⟨.run piL, []⟩ ⟨.run piR, []⟩
      (fun v1 v2 => iprop(⌜v1 = .kont⌝ ∗ ⌜v2 = .kont⌝ ∗ wp k ⟨.run poL, Fl⟩ ⟨.run poR, Fr⟩ Φ))
    ⊢ wp k ⟨.run piL, poL :: Fl⟩ ⟨.run piR, poR :: Fr⟩ Φ := by
  sorry
-/




/-

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

-/


end basicrules


section dwp
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

variable [NMLEnv DataT]

/-- The desynchronized weakest precondition modality (dwp). -/
def dwp (Lm Rm Lx Rx : Nat) (p1 p2 : ProgState DataT) (Φ : ProgState DataT → ProgState DataT → @PROP DataT) :
    @PROP DataT := iprop(
  ∀ s1, ∀ s2, state_interp s1 s2 -∗ |==>
  ∃ p1' p2', Φ p1' p2' ∗ ∃ s1' s2',
    (∃ nl nr, ⌜Lm ≤ nl ∧ Rm ≤ nr ∧ nl ≤ Lx ∧ nr ≤ Rx ∧
      SmallStep.StepN nl (p1, s1) (p1', s1') ∧ SmallStep.StepN nr (p2, s2) (p2', s2')⌝ ) ∗
    state_interp s1' s2')

/-- Introduce a `dwp` around a weakest precondition. -/
theorem wpDesync : ⊢ dwp 1 1 K K p1 p2 (wp K · · Φf) -∗ wp (DataT := DataT) K p1 p2 Φf := by
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
  refine .trans ?_ BIUpdate.intro
  -- Conclude using current resources
  exact sep_symm

/-- Eliminate a `dwp` that has met its minimum step count. -/
theorem wpResync : ⊢ Φ p1 p2 -∗ dwp (DataT := DataT) 0 0 Lx Rx p1 p2 Φ := by
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
theorem dwpPureL (Hstep : SPure p1 p1' HP) (H : HP) (Hx : 0 < Lx := by omega) :
    ⊢ dwp (Lm - 1) Rm (Lx - 1) Rx p1' p2 Φ -∗ dwp (DataT := DataT) Lm Rm Lx Rx p1 p2 Φ := by
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
    refine StepN.step (Hstep sl H) ?_
    trivial
  · iexact Hstate

-- NB. Keeping this code in the repo as an example for writing basic proof rules.
/-- `dwp` for a single pure step on the right. -/
theorem dwpPureR (Hstep : SPure p2 p2' HP) (H : HP) (Hx : 0 < Rx := by omega) :
    ⊢ dwp Lm (Rm - 1) Lx (Rx - 1) p1 p2' Φ -∗ dwp (DataT := DataT) Lm Rm Lx Rx p1 p2 Φ := by
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
    refine StepN.step (Hstep sr H) ?_
    trivial
  · iexact H



open ChipIndex in
/-- `dwp` for a single allocation step on the left. This is a little bit simpler
than the `uwp` version since it quantifies over the generated location. -/
theorem dwpAllocL (Hx : 1 < Lx := by omega) {loc : LocalContext DataT}:
    (∀ ℓₗ, (ℓₗ [S]⇉ₗ∅) -∗
         dwp (Lm - 2) Rm (Lx - 2) Rx ⟨.run ⟨p1', (loc.bindv x (.uptr <| sbufUnboundedIndex ℓₗ))⟩, F⟩ p2 Φ)
    ⊢ dwp (DataT := DataT) Lm Rm Lx Rx ⟨.run ⟨(.assign (.some x) (.alloc Memory.sbuf) :: p1'), loc⟩, F⟩ p2 Φ := by
  sorry
  /-
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
-/

open ChipIndex in
/-- `dwp` for a single allocation step on the left. This is a little bit simpler
than the `uwp` version since it quantifies over the generated location. -/
theorem dwpAllocR (Hx : 1 < Rx := by omega) {loc : LocalContext DataT}:
    (∀ ℓᵣ, (ℓᵣ [S]⇉ᵣ∅) -∗
         dwp Lm (Rm - 2) Lx (Rx - 2) p1 ⟨.run ⟨p2', loc.bindv x (.uptr <| sbufUnboundedIndex ℓᵣ)⟩, F⟩ Φ)
    ⊢ dwp (DataT := DataT) Lm Rm Lx Rx p1 ⟨.run ⟨(.assign (.some x) (.alloc Memory.sbuf) :: p2'), loc⟩, F⟩ Φ := by
  sorry

/-

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
-/

-- theorem dwpTDunopCstL (Hx : 0 < Lx := by omega) :
--      (ℓₗ [S]⇉ₗ∅) ∗ ((ℓₗ [S]⇉ₗ∅) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx ⟨.run ⟨p1', loc⟩, F⟩ p2 Φ)
--     ⊢ dwp (DataT := DataT) Lm Rm Lx Rx ⟨.run ⟨.tsdunop (.var <| L) .cst (.val <| .data d₀):: p1', loc⟩, F⟩ p2 Φ := by
--   sorry


theorem dwpTDunopCstL (Hx : 0 < Lx := by omega) :
     (ℓₗ [S]⇉ₗ∅) ∗ ((ℓₗ [S]⇉ₗ∅) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx ⟨.run ⟨p1', loc⟩, F⟩ p2 Φ)
    ⊢ dwp (DataT := DataT) Lm Rm Lx Rx ⟨.run ⟨.tsdunop (.var <| L) .cst (.val <| .data d₀):: p1', loc⟩, F⟩ p2 Φ := by
  sorry





/-
theorem dwpSetpL {v : DataT} (Hx : 0 < Lx := by omega) :
    ⊢ ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| p1) p2 Φ) -∗
       (⟨i, x⟩ ↦ₗ mv) -∗
       (dwp Lm Rm Lx Rx (.run <| ⟨.setp (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v), loc⟩ :: p1) p2 Φ) := by
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
-/


-- TODO: Turn this into a uwp
theorem dwpSetpL {v : DataT} (Hx : 0 < Lx := by omega) :
    ((⟨i, x⟩ ↦ₗ mv) ∗ ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx ⟨.run ⟨p1, loc⟩, F⟩ p2 Φ))
    ⊢ (dwp Lm Rm Lx Rx ⟨.run ⟨(.setp (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v) :: p1), loc⟩, F⟩ p2 Φ) := by
  -- Unfold the dwp in the conclusion
  iintro ⟨Hmv, Hdwp⟩
  conv => rhs; unfold dwp
  iintro sl sr Hs
  refine include_sep (@update_set_lemma_left DataT ⟨i, x⟩ sl sr mv (some v)) ?_
  -- Add the update lemma to the context
  iintro ⟨Hupd, ⟨Hmv, Hdqp⟩, Hσ⟩
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
  refine ⟨_, ⟨stepN_1_iff_step.mpr ?_, SL⟩⟩
  simp only [Step, NML.step]
  congr

-- TODO: Turn this into a uwp
theorem dwpSetpR {v : DataT} (Hx : 0 < Rx := by omega) :
    ((⟨i, x⟩ ↦ᵣ mv) ∗ ((⟨i, x⟩ ↦ᵣ some v) -∗ dwp Lm (Rm - 1) Lx (Rx - 1) p1 ⟨.run ⟨p2, loc⟩, F⟩ Φ))
    ⊢ (dwp Lm Rm Lx Rx p1 ⟨.run ⟨(.setp (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v) :: p2), loc⟩, F⟩ Φ) := by
  -- Unfold the dwp in the conclusion
  iintro ⟨Hmv, Hdwp⟩
  conv => rhs; unfold dwp
  iintro sl sr Hs
  -- Add the update lemma to the context
  refine include_sep (@update_set_lemma_right DataT ⟨i, x⟩ sl sr mv (some v)) ?_
  iintro ⟨Hupd, ⟨Hmv, Hdwp⟩, Hσ⟩
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
  refine ⟨_, ⟨stepN_1_iff_step.mpr ?_, SR⟩⟩
  simp only [Step, NML.step]
  congr







-- @[simp] abbrev PLoopExit (ctx : LocalContext DataT) (n : Nat) : Prop := ctx.peeki n = none
--
-- theorem SPure.loopExit : SPure (DataT := DataT)
--     ⟨.run ⟨(.loop x (.val <| .iref i) b :: ps), loc⟩, F⟩
--     ⟨.run ⟨ps, loc⟩, F⟩ (PLoopExit loc i) := by
--   intro s H; simp only [Step, step]; rw [H]
--





/-
-- TODO: This is only used for an example right now, a less ad-hoc solution for
-- ExprSteps that use state is necessary.
theorem dwpReadpRetL {v : DataT} (Hx : 0 < Lx := by omega) :
    ⊢ ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| ⟨.ret (.val <| .data v), loc⟩ :: p1) p2 Φ) -∗
      (⟨i, x⟩ ↦ₗ some v) -∗
      (dwp Lm Rm Lx Rx (.run <| ⟨.ret <| .readp (.val <| .uptr i) (.val <| .iptr x), loc⟩ :: p1) p2 Φ) := by
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
    (⟨i, x⟩ ↦ₗ some v) ∗ ((⟨i, x⟩ ↦ₗ some v) -∗ dwp (Lm - 1) Rm (Lx - 1) Rx (.run <| ⟨.ret (.val <| .data v), loc⟩ :: p1) p2 Φ)
    ⊢ (dwp Lm Rm Lx Rx (.run <| ⟨.ret <| .readp (.val <| .uptr i) (.val <| .iptr x), loc⟩ :: p1) p2 Φ) := by
  apply BI.wand_entails
  apply Entails.trans (dwpReadpRetL (v := v))
  istart
  iintro H1 ⟨H2, H3⟩
  iapply H1 with [H3]
  · iexact H3
  · iexact H2

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

-/

-- /- Proposition over locals. Used for generalization.
-- LocProp should be solvable by `simp` for good automation. -/
-- def LocProp (DataT : Type _) := @NML.Locals DataT → Prop
-- @[simp] nonrec def LocProp.True : LocProp DataT := fun _ => True
-- @[simp] def LocProp.And (p1 p2 : LocProp DataT) : LocProp DataT := fun loc => p1 loc ∧ p2 loc
-- @[simp] def LocProp.Inc (s : String) (v : @Value DataT) : LocProp DataT := fun loc => loc s = some v
-- @[simp] def LocProp.Emp (s : String) : LocProp DataT := fun loc => loc s = none


/-- Generalize a wp by a relationship on its locations -/
theorem wp_gen_loc (R : LocalContext DataT → LocalContext DataT → Prop) :
  ⊢ (∀ locₗ locᵣ, ⌜R locₗ locᵣ⌝ -∗ wp (DataT := DataT) K ⟨.run ⟨(sₗ :: pₗ), locₗ⟩, F⟩ ⟨.run ⟨(sᵣ :: pᵣ), locᵣ⟩, F⟩ Φ) -∗
    ⌜R llₗ llᵣ⌝ -∗
    wp (DataT := DataT) K ⟨.run ⟨(sₗ :: pₗ), llₗ⟩, F⟩ ⟨.run ⟨(sᵣ :: pᵣ), llᵣ⟩, F⟩ Φ := by
  iintro H HR
  ispecialize H _ _ HR
  iexact H


end dwp




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
  prog  : NML.ProgState DataT
  prog' : NML.ProgState DataT
  steps : Nat

/-- A `uwp` that uses its resources to take steps on the left. -/
structure uwpL (DataT : Type _) [NMLEnv DataT] extends uwp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∃ σₗ', ⌜SmallStep.StepN steps (prog, σₗ) (prog', σₗ')⌝ ∗ |==> (state_interp σₗ' σᵣ ∗ post)))

/-- A `uwp` that uses its resources to take steps on the right. -/
structure uwpR (DataT : Type _) [NMLEnv DataT] extends uwp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∃ σᵣ', ⌜SmallStep.StepN steps (prog, σᵣ) (prog', σᵣ')⌝ ∗ |==> (state_interp σₗ σᵣ' ∗ post)))

/-- StackFrames that have a canonical UWP for symbolic head reduction -/
structure SymbolicL (DataT : Type _) [NMLEnv DataT] (prog prog' : NML.StackFrame DataT) (pre post : PROP DataT) (steps : Nat) where
  spec F : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∃ σₗ', ⌜SmallStep.StepN (Val := Value DataT) (Prog := ProgState DataT) steps (⟨.run prog, F⟩, σₗ) (⟨.run prog', F⟩, σₗ')⌝ ∗
       |==> (state_interp σₗ' σᵣ ∗ post)))

def SymbolicL.uwpL {DataT : Type _} [NMLEnv DataT] {prog prog' : NML.StackFrame DataT}
    {pre post : PROP DataT} (SL : SymbolicL DataT prog prog' pre post steps)
    (F : List (StackFrame DataT)) : uwpL DataT where
  pre := pre
  post := post
  prog := ⟨.run prog, F⟩
  prog' := ⟨.run prog', F⟩
  steps := steps
  spec := SL.spec F

/-- StackFrames that have a canonical UWP for symbolic execution -/
structure SymbolicR (DataT : Type _) [NMLEnv DataT]  (prog prog' : NML.StackFrame DataT) (pre post : PROP DataT) (steps : Nat) where
  spec F : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∃ σᵣ', ⌜SmallStep.StepN (Val := Value DataT) (Prog := ProgState DataT) steps (⟨.run prog, F⟩, σᵣ) (⟨.run prog', F⟩, σᵣ')⌝ ∗
      |==> (state_interp σₗ σᵣ' ∗ post)))

def SymbolicR.uwpR {DataT : Type _} [NMLEnv DataT] {prog prog' : NML.StackFrame DataT}
    {pre post : PROP DataT} (SR : SymbolicR DataT prog prog' pre post steps)
    (F : List (StackFrame DataT)) : uwpR DataT where
  pre := pre
  post := post
  prog := ⟨.run prog, F⟩
  prog' := ⟨.run prog', F⟩
  steps := steps
  spec := SR.spec F

-- TODO: Make SymbolicL/R instances for all of my uwp's if this turns out to be a good way to do things

section uwp

open Iris Iris.BI Iris.BI.BIBase KLR.Core Iris NML SmallStep

variable {DataT : Type _} [NMLEnv DataT]

-- TODO: Inline into dwpL
/-- Step the left-hand side of a dwp using a `uwpL`. -/
theorem dwpL' (u : uwpL DataT) (Hx : u.steps ≤ Lx) :
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

theorem dwpL (u : uwpL DataT) (Hx : u.steps ≤ Lx) :
    u.pre ∗ (u.post -∗ dwp (Lm - u.steps) Rm (Lx - u.steps) Rx u.prog' pr Φ) ⊢
    dwp Lm Rm Lx Rx u.prog pr Φ := (wand_entails <| dwpL' u Hx)

-- TODO: Inline into dwpR
/-- Step the right-hand side of a dwp using a `uwpR`. -/
theorem dwpR' (u : uwpR DataT) (Hx : u.steps ≤ Rx) :
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

theorem dwpR (u : uwpR DataT) (Hx : u.steps ≤ Rx) :
    u.pre ∗ (u.post -∗ dwp Lm (Rm - u.steps) Lx (Rx - u.steps) pl u.prog' Φ)
    ⊢ dwp Lm Rm Lx Rx pl u.prog Φ :=
  (wand_entails <| dwpR' u Hx)

@[simp] def SPure.uwpL {p p' : Prog DataT} (H : SPure p p' H') (HH' : H') : uwpL DataT where
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
      exact stepN_1_iff_step.mpr <| H σₗ HH'
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

@[simp] def SPure.uwpR {p p' : Prog DataT} (H : SPure p p' H') (HH' : H') : uwpR DataT where
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
      exact stepN_1_iff_step.mpr <| H σᵣ HH'
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ


-- @[simp] def
  -- dwp 0 0 2 3
  --   {
  --     current :=
  --       ExecState.run
  --         ([Stmt.tsdunop (Expr.var "ℓ") TSDunop.cst (Expr.val (Value.data d₀)),
  --             Stmt.loop "z" (Expr.val (Value.iref 1)) [Stmt.tsdunop (Expr.var "ℓ") TSDunop.add (Expr.var "z")],
  --             NML.Stmt.ret ((Expr.var "ℓ").readp (Expr.val (Value.iptr (0, 0))))],
  --           { loc := LocalContext.emp.loc.bind "ℓ" (Value.uptr (ChipIndex.sbufUnboundedIndex ℓₗ)),
  --             it := LocalContext.emp.it.bind 1 (some (IteratorS.affineRange 1 2 3).toIterator) }),
  --     context := [] }

-- .uwpL {p p' : Prog DataT} (H : SPure p p' H') (HH' : H') : uwpL DataT where


def SPure.SymbolicL (sf sf' : StackFrame DataT) (H : ∀ F, SPure ⟨.run sf, F⟩ ⟨.run sf', F⟩ H') (HH' : H') :
    SymbolicL DataT sf iprop(True) iprop(True) (prog' := sf') 1 where
  spec := by
    intro F
    iintro σₗ σᵣ %_ Hσ
    iexists σₗ
    isplit r
    · ipure_intro
      exact stepN_1_iff_step.mpr <| H _ σₗ HH'
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

def SPure.SymbolicR (sf sf' : StackFrame DataT) (H : ∀ F, SPure ⟨.run sf, F⟩ ⟨.run sf', F⟩ H') (HH' : H') :
    SymbolicR DataT sf iprop(True) iprop(True) (prog' := sf') 1 where
  spec := by
    intro F
    iintro σₗ σᵣ %_ Hσ
    iexists σᵣ
    isplit r
    · ipure_intro
      apply stepN_1_iff_step.mpr
      apply H _ σᵣ HH'
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

-- def SymbolicL.setp : SymbolicL DataT
--       ⟨.setp (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v) :: pl, ctx⟩
--       ⟨pl, ctx⟩
--       (⟨i, x⟩ ↦ₗ mv)
--       (⟨i, x⟩ ↦ₗ some v)
--       1 where
--   spec := sorry -- TODO: Copy over the below proof from dwp setpR
--
-- def SymbolicR.setp : SymbolicL DataT
--       ⟨.setp (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v) :: pr, ctx⟩
--       ⟨pl, ctx⟩
--       (⟨i, x⟩ ↦ᵣ mv)
--       (⟨i, x⟩ ↦ᵣ some v)
--       1 where
--   spec := sorry -- TODO: Copy over the below proof from dwp setpR

-- def SymbolicL.tsdunop_add : SymbolicL DataT
--       ⟨.tsdunop (.val <| .uptr i) .add (.val <| .int z) :: pl, ctx⟩
--       ⟨pl, ctx⟩
--       (i ⇉ₗ (.some st))
--       (i ⇉ₗ (.some <| TSDunop.app_addZ st z))
--       1 where
--   spec := sorry -- TODO
--
-- def SymbolicL.tsdunop_cst : SymbolicL DataT
--       ⟨.tsdunop (.val <| .uptr i) .cst (.val <| .data d) :: pl, ctx⟩
--       ⟨pl, ctx⟩
--       (i ⇉ₗ mz)
--       (i ⇉ₗ (.some <| TSDunop.app_cst d))
--       1 where
--   spec := sorry -- TODO

end uwp

section ewp

/-! ewp

Often, the uwp step you want to take amounts to stepping one of its subexpressions.
Instead of describing the stepping rules for every expression in every context, the ewp
abstraction is a simple way to define uwp's of this form.

The main items in this section:

- SmallStep.ExprLift: a statement about an statment with a hole, which says that steps of an
  expression remain in that hole.

- ewp, ewpL, ewpR: a spec for an expression, independent of its context. The spec also quantifies
  over the local enviornments this step can take place in.

-- liftE, lfitEL, liftER: Combine an ExprLift expression and an `ewp` to get a `uwp`.
-/

open Iris Iris.BI Iris.BI.BIBase KLR.Core Iris NML SmallStep

-- Like UWP but for ExprStep
structure ewp (DataT : Type _) where
  pre   : PROP DataT
  post  : PROP DataT
  expr  : NML.Expr DataT
  -- Using a predicate on locations instead of a single location becase
  -- we do not have separating conjunction over them.
  locP  : NML.LocalContext DataT → Prop
  expr' : NML.Expr DataT

/-- An `ewp` that uses its resources to take steps on the left. -/
structure ewpL (DataT : Type _) [NMLEnv DataT] extends ewp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∀ loc, ∃ σₗ', ⌜locP loc → ExprStep expr loc σₗ = .some (expr', σₗ')⌝ ∗ |==> (state_interp σₗ' σᵣ ∗ post)))

/-- An `ewp` that uses its resources to take steps on the left. -/
structure ewpR (DataT : Type _) [NMLEnv DataT] extends ewp DataT where
  spec : ⊢ iprop(∀ σₗ σᵣ, pre -∗ state_interp σₗ σᵣ -∗
    (∀ loc, ∃ σᵣ', ⌜locP loc → ExprStep expr loc σᵣ = .some (expr', σᵣ')⌝ ∗ |==> (state_interp σₗ σᵣ' ∗ post)))

@[simp] def liftE (e : ewp DataT) (p : Expr DataT → Stmt DataT)
    (ps : List (NML.Stmt DataT)) (loc : NML.LocalContext DataT) (F : List (StackFrame DataT)) : uwp DataT where
  pre   := e.pre
  post  := e.post
  prog  := ⟨.run ⟨(p e.expr :: ps), loc⟩, F⟩
  prog' := ⟨.run ⟨(p e.expr' :: ps), loc⟩, F⟩
  steps := 1

/-- Lift an `ewpL` to a `uwpL` provided the context is `ExprLift` -/
@[simp] def liftEL [NMLEnv DataT] (e : ewpL DataT) {p : Expr DataT → Stmt DataT} (Hp : EPLift p) {ps : List (NML.Stmt DataT)}
     {loc : NML.LocalContext DataT} {F : List (StackFrame DataT)} (Hloc : e.locP loc := by simp) : uwpL DataT where
  touwp := liftE e.toewp p ps loc F
  spec  := by
    apply Entails.trans e.spec ?_
    simp only [liftE]
    iintro Hspec σₗ σᵣ Hpre Hσ
    ispecialize Hspec σₗ σᵣ Hpre Hσ loc
    icases Hspec with ⟨Hσₗ', %Hstep, Hupd⟩
    iexists Hσₗ'
    isplit r
    · ipure_intro
      refine stepN_1_iff_step.mpr (Hp <| Hstep Hloc)
    · iexact Hupd

/-- Lift an `ewpR` to a `uwpR` provided the context is `ExprLift` -/
@[simp] def liftER [NMLEnv DataT] (e : ewpR DataT) {p : Expr DataT → Stmt DataT} (Hp : EPLift p) {ps : List (NML.Stmt DataT)}
    {loc : NML.LocalContext DataT} {F : List (StackFrame DataT)} (Hloc : e.locP loc := by simp) : uwpR DataT where
  touwp := liftE e.toewp p ps loc F
  spec  := by
    apply Entails.trans e.spec ?_
    simp only [liftE]
    iintro Hspec σₗ σᵣ Hpre Hσ
    ispecialize Hspec σₗ σᵣ Hpre Hσ loc
    icases Hspec with ⟨Hσᵣ', %Hstep, Hupd⟩
    iexists Hσᵣ'
    isplit r
    · ipure_intro
      exact stepN_1_iff_step.mpr (Hp <| Hstep Hloc)
    · iexact Hupd

@[simp] def EPLift.uwpL [NMLEnv DataT] {p : Expr DataT → Stmt DataT} (Hp : EPLift p) (e : ewpL DataT) {ps : List (NML.Stmt DataT)}
     {loc : NML.LocalContext DataT} {F : List (StackFrame DataT)} (Hloc : e.locP loc := by simp) : uwpL DataT :=
  liftEL e Hp (Hloc := Hloc) (ps := ps) (F := F)

@[simp] def EPLift.uwpR [NMLEnv DataT] {p : Expr DataT → Stmt DataT} (Hp : EPLift p) (e : ewpR DataT) {ps : List (NML.Stmt DataT)}
     {loc : NML.LocalContext DataT} {F : List (StackFrame DataT)} (Hloc : e.locP loc := by simp) : uwpR DataT :=
  liftER e Hp (Hloc := Hloc) (ps := ps) (F := F)

@[deprecated "Use EPure.ewpL instead. " (since:="2025/08/09") ]
def ewpVarL [NMLEnv DataT] {s : String} (v : Value DataT) : ewpL DataT where
  pre   := iprop(True)
  post  := iprop(True)
  expr  := .var s
  locP  := (·.getv s = some v)
  expr' := .val v
  spec  := by
    iintro σₗ σᵣ %_ Hσ loc
    iexists σₗ
    isplit r
    · ipure_intro
      intro H; simp only [ExprStep]; rw [H]; simp
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ
attribute [simp] ewpVarL

@[deprecated "Use EPure.ewpR instead. " (since:="2025/08/09") ]
def ewpVarR [NMLEnv DataT] {s : String} (v : Value DataT) : ewpR DataT where
  pre   := iprop(True)
  post  := iprop(True)
  expr  := .var s
  locP  := (·.getv s = some v)
  expr' := .val v
  spec  := by
    iintro σₗ σᵣ - Hσ loc
    iexists σᵣ
    isplit r
    · ipure_intro
      intro H; simp only [ExprStep]; rw [H]; simp
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ
attribute [simp] ewpVarR


@[simp] def EPure.ewpL [NMLEnv DataT] (E : EPure (DataT := DataT) e e' HP) : ewpL DataT where
  pre   := iprop(True)
  post  := iprop(True)
  expr  := e
  expr' := e'
  locP  := HP
  spec  := by
    iintro σₗ σᵣ - Hσ loc
    iexists σₗ
    isplit r
    · ipure_intro
      intro H
      apply E
      apply H
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

@[simp] def EPure.ewpR [NMLEnv DataT] (E : EPure (DataT := DataT) e e' HP) : ewpR DataT where
  pre   := iprop(True)
  post  := iprop(True)
  expr  := e
  expr' := e'
  locP  := HP
  spec  := by
    iintro σₗ σᵣ - Hσ loc
    iexists σᵣ
    isplit r
    · ipure_intro
      intro H
      apply E
      apply H
    · refine .trans ?_ BIUpdate.intro
      refine .trans ?_ sep_true.mpr
      iintro Hσ
      iexact Hσ

@[simp] def EELift.ewpL [NMLEnv DataT] {p : Expr DataT → Expr DataT} (EL : EELift p) (E : ewpL DataT) : ewpL DataT where
  pre   := E.pre
  post  := E.post
  expr  := p E.expr
  expr' := p E.expr'
  locP  := E.locP
  spec  := by
    apply Entails.trans E.spec ?_
    iintro Hspec σₗ σᵣ Hpre Hσ loc
    ispecialize Hspec σₗ σᵣ Hpre Hσ loc
    icases Hspec with ⟨σₗ', %Hstep, Hupd⟩
    iexists σₗ'
    isplit r
    · ipure_intro
      intro H
      apply EL
      apply Hstep
      apply H
    · iexact Hupd

@[simp] def EELift.ewpR [NMLEnv DataT] {p : Expr DataT → Expr DataT} (EL : EELift p) (E : ewpR DataT) : ewpR DataT where
  pre   := E.pre
  post  := E.post
  expr  := p E.expr
  expr' := p E.expr'
  locP  := E.locP
  spec  := by
    apply Entails.trans E.spec ?_
    iintro Hspec σₗ σᵣ Hpre Hσ loc
    ispecialize Hspec σₗ σᵣ Hpre Hσ loc
    icases Hspec with ⟨σₗ', %Hstep, Hupd⟩
    iexists σₗ'
    isplit r
    · ipure_intro
      intro H
      apply EL
      apply Hstep
      apply H
    · iexact Hupd


@[simp] def ewp.deref_storeL [NMLEnv DataT] (ℓ : ChipIndex) (s : LocalStore DataT) : ewpL DataT where
  pre   := iprop(ℓ ⇉ₗ some s)
  post  := iprop(ℓ ⇉ₗ some s)
  expr  := .deref_store (.val <| .uptr ℓ)
  expr' := .val <| .tens s
  locP  := fun _ => True
  spec  := by sorry


@[simp] def ewp.deref_storeR [NMLEnv DataT] (ℓ : ChipIndex) (s : LocalStore DataT) : ewpR DataT where
  pre   := iprop(ℓ ⇉ᵣ some s)
  post  := iprop(ℓ ⇉ᵣ some s)
  expr  := .deref_store (.val <| .uptr ℓ)
  expr' := .val <| .tens s
  locP  := fun _ => True
  spec  := by sorry

/-
Remaining expressions
  /- Read point from memory -/
  | .readp (.val <| .uptr c) (.val <| .iptr i) =>
      s.memory.get ⟨c, i⟩ |>.bind fun vd =>
      some ⟨.val <| .data vd, s⟩
-/


end ewp
