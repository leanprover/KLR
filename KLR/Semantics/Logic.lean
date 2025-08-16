/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Memory
import Iris.Algebra.OFE
import Iris.Algebra.Agree
import Iris.Algebra.UPred
import Iris.Instances.UPred
import Iris.Instances.heProp
import Iris.BI
import Iris.ProofMode
import Iris.ProofMode.Tactics.Apply
import Iris.BI.DerivedLaws
import Iris.BI.Updates
import Iris.Algebra.CMRA
import Iris.Algebra.View
import Iris.Algebra.HeapView

-- TODO: Erasure
-- TODO: Monotonicity of wp with respect to K (compose WP's with max )
-- TOOD: Pure-pure proof rules

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML

abbrev Prog DataT := (ProgState DataT)

variable {DataT : Type _} [NMLEnv DataT]

abbrev PROP (DataT : Type _)  : Type _ := heProp PNat ProdNeuronIndex DataT ProdNeuronMemory
abbrev PROPR (DataT : Type _) : Type := (HeapView PNat ProdNeuronIndex (Agree (LeibnizO DataT)) ProdNeuronMemory)

-- The state interpretation, ie the global version of the program state.
def state_interp (left right : State DataT) : PROP DataT :=
  heProp_auth _ _ _ _ (.mk left.memory right.memory)

def state_frag (left right : State DataT) : PROP DataT :=
  heProp_frag _ _ _ _ (.mk left.memory right.memory)

/-- PointsTo for a single element in the store -/
def PointsTo (k : ProdNeuronIndex) (v : Option DataT) : PROP DataT :=
  heProp_frag _ _ _ _ (Heap.point k v)

notation k " ↦ " v => PointsTo k v
notation k " ↦ₗ " v => PointsTo (ProdIndex.left k) v
notation k " ↦ᵣ " v => PointsTo (ProdIndex.right k) v

/-- PointsTo that asserts knowledge over an entire store.
When using unbounded and HBM allocations, this is probably enough. -/
def PointsToS (k : ProdIndex ChipIndex) (v : Option (LocalStore DataT)) : PROP DataT :=
  match k with
  | .left  i => heProp_frag _ _ _ _ ⟨(ChipMemory.set_store ChipMemory.empty i v), ChipMemory.empty⟩
  | .right i => heProp_frag _ _ _ _ ⟨ChipMemory.empty, (ChipMemory.set_store ChipMemory.empty i v)⟩

-- TODO: Refactor to deduplicate
notation k " ⇉ " v      => PointsToS k v
notation k " ⇉∅ "       => PointsToS k none

notation k " ⇉ₗ " v     => PointsToS (ProdIndex.left  k) v
notation k " ⇉ₗ∅  "     => PointsToS (ProdIndex.left  k) none
notation k " [S]⇉ₗ " v  => PointsToS (ProdIndex.left  (ChipIndex.sbufUnboundedIndex k)) (some v)
notation k " [P]⇉ₗ " v  => PointsToS (ProdIndex.left  (ChipIndex.psumUnboundedIndex k)) (some v)
notation k " [H]⇉ₗ " v  => PointsToS (ProdIndex.left  (ChipIndex.hbmUnboundedIndex k))  (some v)
notation k " [S]⇉ₗ∅ "   => PointsToS (ProdIndex.left  (ChipIndex.sbufUnboundedIndex k)) none
notation k " [P]⇉ₗ∅ "   => PointsToS (ProdIndex.left  (ChipIndex.psumUnboundedIndex k)) none
notation k " [H]⇉ₗ∅ "   => PointsToS (ProdIndex.left  (ChipIndex.hbmUnboundedIndex k))  none

notation k " ⇉ᵣ " v     => PointsToS (ProdIndex.right k) v
notation k " ⇉ᵣ∅  "     => PointsToS (ProdIndex.right k) none
notation k " [S]⇉ᵣ " v  => PointsToS (ProdIndex.right (ChipIndex.sbufUnboundedIndex k)) (some v)
notation k " [P]⇉ᵣ " v  => PointsToS (ProdIndex.right (ChipIndex.psumUnboundedIndex k)) (some v)
notation k " [H]⇉ᵣ " v  => PointsToS (ProdIndex.right (ChipIndex.hbmUnboundedIndex k))  (some v)
notation k " [S]⇉ᵣ∅ "   => PointsToS (ProdIndex.right (ChipIndex.sbufUnboundedIndex k)) none
notation k " [P]⇉ᵣ∅ "   => PointsToS (ProdIndex.right (ChipIndex.psumUnboundedIndex k)) none
notation k " [H]⇉ᵣ∅ "   => PointsToS (ProdIndex.right (ChipIndex.hbmUnboundedIndex k))  none


/-

WIP Adding continuations to the WP

I think adding an extra value form for (.run [] _) might be less invasive actually.


/-- Lift a postcondition on values to a postcondition on continuations -/
def ΦRet(Φ : Value DataT → Value DataT → PROP DataT) (mv1 mv2 : Option (Value DataT)) : PROP DataT :=
  iprop(∃ v1 v2, ⌜mv1 = .some v1 ⌝ ∗ ⌜mv2 = .some v2⌝ ∗ Φ v1 v2)

def toCont : Prog DataT → Option (Option (Value DataT))
-- Program is an early return, value postcondition must hold
| .done v  => .some (.some v)
-- Program is stuck because it has reached the end of the frame, frame postcondition must hold
| .run [] _ => .some .none
-- Program is still running
| _ => .none

theorem toCont_some_toVal {p : Prog DataT} :
    toCont p = .some (.some v) ↔ toVal p = .some v := by
  cases p <;> simp [toCont, toVal]; intro H
  rename_i p' _; cases p' <;> simp at H

def wp_F (wp : LeibnizO Nat → Prog DataT → Prog DataT → (Option (Value DataT) → Option (Value DataT) → PROP DataT) → PROP DataT)
  (K : LeibnizO Nat) (p1 p2 : Prog DataT) (Φf : Option (Value DataT) → Option (Value DataT) → PROP DataT) : PROP DataT := iprop(
      (|==> ∃ mvl, ∃ mvr, ⌜toCont p1 = .some mvl⌝ ∗ ⌜toCont p2 = some mvr ⌝ ∗ Φf mvl mvr) ∨
      (∀ sl, ∀ sr, state_interp sl sr -∗ |==>
       ∃ cl', ∃ cr', ∃ nl, ∃ nr, ⌜0 < nl ∧ 0 < nr ∧ nl ≤ K.car ∧ nr ≤ K.car ∧
         SmallStep.StepN nl (p1, sl) cl' ∧ SmallStep.StepN nr (p2, sr) cr'⌝ ∗
         ▷ (state_interp cl'.2 cr'.2 ∗ wp K cl'.1 cr'.1 Φf)))
-/


/--
Definition of the weakest precondition.

For any pair of configurations, either both programs are values satisfying the postcondition,
or for all states satisfying the current interp,
the state can be updated to obtain the state after executing between 1 and k steps on both sides,
and ending up in a pair of configurations that satisfy the weakest precondition. -/
def wp_F (wp : Nat → Prog DataT → Prog DataT → (Value DataT → Value DataT → PROP DataT) → PROP DataT)
  (K : Nat) (p1 p2 : Prog DataT) (Φf : Value DataT → Value DataT → PROP DataT) : PROP DataT := iprop(
      (|==> ∃ vl, ∃ vr, ⌜toVal p1 = .some vl⌝ ∗ ⌜toVal p2 = some vr ⌝ ∗ Φf vl vr) ∨
      (∀ sl, ∀ sr, state_interp sl sr -∗ |==>
       ∃ cl', ∃ cr', ∃ nl, ∃ nr, ⌜0 < nl ∧ 0 < nr ∧ nl ≤ K ∧ nr ≤ K ∧
         SmallStep.StepN nl (p1, sl) cl' ∧ SmallStep.StepN nr (p2, sr) cr'⌝ ∗
         ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp K cl'.1 cr'.1 Φf)))

instance wp_contractive : Iris.OFE.Contractive (α := Nat → Prog DataT → Prog DataT → (Value DataT → Value DataT → PROP DataT) → PROP DataT) wp_F := by
  sorry

/-- Definition of the weakest precondition -/
def wp (K : Nat) (p1 p2 : Prog DataT) (Φf : Value DataT → Value DataT → PROP DataT) : PROP DataT :=
  (Iris.fixpoint wp_F) K p1 p2 Φf

theorem wp_unfold {K : Nat} {p1 p2 : Prog DataT} {Φf : Value DataT → Value DataT → PROP DataT} :
    wp K p1 p2 Φf ≡ iprop(
      (|==> ∃ vl, ∃ vr, ⌜toVal p1 = some vl⌝ ∗ ⌜toVal p2 = some vr⌝ ∗ Φf vl vr) ∨
      ( ∀ sl, ∀ sr, state_interp sl sr -∗ |==>
        ∃ cl', ∃ cr', ∃ nl, ∃ nr,
          ⌜0 < nl ∧ 0 < nr ∧ nl ≤ K ∧ nr ≤ K ∧ SmallStep.StepN nl (p1, sl) cl' ∧ SmallStep.StepN nr (p2, sr) cr'⌝ ∗
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp K cl'.1 cr'.1 Φf))) := by
  apply fixpoint_unfold (f := ⟨wp_F, OFE.ne_of_contractive wp_F⟩)

end weakestpre

section adequacy

open Iris BI NML BIBase SmallStep

variable [NMLEnv DataT]

/-- Step 1 of the adequacy argument:
Turn a proof of the wp in the logic into a relationship between the two programs, under some modalities and
with a ``state_interp sl sr` precondition. -/
theorem wp_to_fupd_PRelS :
    wp (DataT := DataT) K pl pr (iprop(⌜Φf · ·⌝)) ⊢ state_interp (DataT := DataT) sl sr -∗
    |==> ▷^[n] ⌜PRelS n K (pl, sl) (pr, sr) Φf ⌝ := by
  revert pl pr sl sr
  induction n with | zero => ?_ | succ n IH => ?_
  · -- Base case: n=0, postcondition is trivial
    intros
    iintro Hwp Hσ
    iclear Hwp
    iclear Hσ
    exact BIUpdate.intro
  · -- Inductive case
    intro pl pr sl sr
    -- Unfold the weakest precondition
    apply (equiv_iff.mp wp_unfold).mp.trans
    istart
    iintro Hwp Hσ
    -- Consider the value and step cases separately
    icases Hwp with ⟨H|H⟩
    · -- Both programs are values
      iclear Hσ
      -- Strip the update modality from the postcondition and remaining hypotheses
      istop; apply BIUpdate.mono; istart
      iintro ⟨vl, vr, %Hvl, %Hvr, %HΦ⟩
      -- Strip the `▷^[·] ·` modality
      istop; refine .trans ?_ laterN_intro; istart
      -- The postcondition is pure, and holds by HΦ
      ipure_intro
      simp [PRelS, Hvl, Hvr, HΦ]
    · -- Both programs can step
      -- Eliminate the update modality from H while keeping it in the conclusion
      ispecialize H sl sr Hσ
      refine (emp_sep.mp.trans <| BIUpdate.mono ?_).trans BIUpdate.trans
      iintro ⟨cl', cr', nl, nr, ⟨%Hnl0, %Hnr0, %HnlK, %HnrK, %HSl, %HSr⟩, H⟩
      -- It suffices to prove the theorem on the continuation
      have Hcont (H : PRelS n K cl' cr' Φf) : PRelS (n + 1) K (pl, sl) (pr, sr) Φf := by
        simp only [stepN_toVal_none Hnl0 HSl, stepN_toVal_none Hnr0 HSr, PRelS]
        exists nl; exists nr; exists cl'; exists cr'
      refine .trans ?_ (BIUpdate.mono <| later_mono <| laterN_mono <| pure_mono <| Hcont)
      -- Apply the IH
      -- apply BIUpdate.mono
      refine .trans ?_ later_bupd_comm_plain
      refine later_mono ?_
      refine .trans ?_ bupd_idem.mp
      apply BIUpdate.mono
      exact wand_elim' IH


open KLR.Core HasHHMap in
/-- Step 2 of the adequacy argument:
If we can prove the postcondition of `wp_to_fupd_PRelS` using any starting state, then
we get that relationship for all step indices `n`. -/
theorem wp_adequacy_pre
    (H : ∀ n, (state_interp (DataT := DataT) sl sr ∗ state_frag sl sr ⊢ |==> ▷^[n] ⌜PRelS n K (pl, sl) (pr, sr) Φf⌝)) :
    ∀ n, PRelS (Prog := Prog DataT) n K (pl, sl) (pr, sr) Φf := by
  -- The initial state to equip the separation logic proof with.
  let σ : PROPR DataT :=
    (●V hhmap (fun _ v => some (toAgree <| LeibnizO.mk v)) <| ProdStore.mk sl.1 sr.1) •
    (◯V hhmap (fun _ v => some (DFrac.own 1, toAgree <| LeibnizO.mk v)) <| ProdStore.mk sl.1 sr.1)
  -- The initial state is valid
  have Hσ : ✓ σ := by
    refine View.view_both_valid.mpr (fun n k => ?_)
    simp [toHeapPred, hhmap_get]
    cases h : (Store.get (⟨sl.1, sr.1⟩ : ProdNeuronMemory _) k)
    · simp
    · simp; exists Iris.DFrac.own 1
  intro n
  -- Apply an Iris soundness theorem for the pure modality, setting the initial ghost state.
  refine UPred.soundness_pure_gen (n := n) Hσ.validN ?_
  -- Apply an Iris soundness theorem for the ▷^[·] modality
  refine UPred_adequacy_laterN_gen (N := n) Hσ _ ?_
  -- Apply an Iris soundness theorem for the |==> modality
  refine bupd_gen_soundness _ _ ?_
  -- Apply the hypothesis H
  refine .trans ?_ (H n)
  -- Conclude by combining the ghost state
  exact (UPred.ownM_op _ _).mp

/-- Main adequacy theorem
To prove that two programs are PRel-related, it suffices to do an Iris proof of a weakest precondition,
starting with heap access to their initial state.  -/
theorem wp_adequacy
    (H : state_frag (DataT := DataT) sl sr ⊢ wp K pl pr (iprop(⌜Φf · ·⌝))) :
    PRel (pl, sl) (pr, sr) Φf := by
  -- Apply the approximation theorems
  refine PrelNLimit (K := K) (fun n => ?_)
  refine PRelNS n ?_
  -- Apply the pre-adequacy theorem
  refine wp_adequacy_pre (fun n' => ?_) n
  -- Convert the goal to a wp using wp_to_fupd_PRelS
  refine sep_comm.mp.trans (wand_elim <| .trans ?_ wp_to_fupd_PRelS)
  exact H

end adequacy

-- /-- Definition for Hoare Triple -/
-- def triple  (pre : PROP DataT) K (p1 p2 : Prog DataT) post :=
--   iprop(pre -∗ wp K p1 p2 post)
--
-- macro "{{ " pre:term  " }} " p1:term " × " p2:term "{{ " x:ident  " => " post:term " }} " : term => do
--   ``(triple $pre $p1 $p2 (fun $x => $post))
