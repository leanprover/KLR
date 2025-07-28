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
import Iris.BI.DerivedLaws
import Iris.BI.Updates
import Iris.Algebra.CMRA
import Iris.Algebra.View
import Iris.Algebra.HeapView

-- The logic: I can reuse UPred with a fixed ghost state (first-order)

-- TODO: Erasure
-- TODO: Monotonicity of wp with respect to K (compose WP's with max )
-- TOOD: Pure-pure proof rules

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML

abbrev Prog DataT := (ExecState DataT)

variable {DataT : Type _}

abbrev PROP (DataT : Type _)  : Type _ := heProp PNat ProdNeuronIndex DataT ProdNeuronMemory
abbrev PROPR (DataT : Type _) : Type := (HeapView PNat ProdNeuronIndex (Agree (LeibnizO DataT)) ProdNeuronMemory)

-- The state interpretation, ie the global version of the program state.
def state_interp (left right : State DataT) : PROP DataT :=
  heProp_auth _ _ _ _ (.mk left.memory right.memory)

def state_frag (left right : State DataT) : PROP DataT :=
  heProp_frag _ _ _ _ (.mk left.memory right.memory)

/-- PointsTo for a single element in the store -/
def PointsTo (k : ProdNeuronIndex) (v : DataT) : PROP DataT :=
  heProp_elem _ _ _ _ k v
notation k " ↦ " v => PointsTo k v
notation k " ↦ₗ " v => PointsTo (ProdIndex.left k) v
notation k " ↦ᵣ " v => PointsTo (ProdIndex.right k) v

/-- PointsTo that asserts knowledge over an entire store.
When using unbounded and HBM allocations, this is probably enough. -/
def PointsToS (k : ProdIndex ChipIndex) (v : Option (LocalStore DataT)) : PROP DataT :=
  match k with
  | .left  i => heProp_frag _ _ _ _ ⟨(ChipMemory.set_store ChipMemory.empty i v), ChipMemory.empty⟩
  | .right i => heProp_frag _ _ _ _ ⟨ChipMemory.empty, (ChipMemory.set_store ChipMemory.empty i v)⟩
notation k " ⇉ " v  => PointsToS k v
notation k " ⇉ₗ " v => PointsToS (ProdIndex.left  k) v
notation k " ⇉ᵣ " v => PointsToS (ProdIndex.right k) v

/- Chip-specific notations, (TODO: Refactor )-/
notation k " [S]⇉ₗ " v  => PointsToS (ProdIndex.left  (ChipIndex.sbufUnboundedIndex k)) (some v)
notation k " [P]⇉ₗ " v  => PointsToS (ProdIndex.left  (ChipIndex.psumUnboundedIndex k)) (some v)
notation k " [H]⇉ₗ " v  => PointsToS (ProdIndex.left  (ChipIndex.hbmUnboundedIndex k))  (some v)

notation k " [S]⇉ᵣ " v  => PointsToS (ProdIndex.right (ChipIndex.sbufUnboundedIndex k)) (some v)
notation k " [P]⇉ᵣ " v  => PointsToS (ProdIndex.right (ChipIndex.psumUnboundedIndex k)) (some v)
notation k " [H]⇉ᵣ " v  => PointsToS (ProdIndex.right (ChipIndex.hbmUnboundedIndex k))  (some v)

notation k " [S]⇉ₗ∅ " => PointsToS (ProdIndex.left  (ChipIndex.sbufUnboundedIndex k)) none
notation k " [P]⇉ₗ∅ " => PointsToS (ProdIndex.left  (ChipIndex.psumUnboundedIndex k)) none
notation k " [H]⇉ₗ∅ " => PointsToS (ProdIndex.left  (ChipIndex.hbmUnboundedIndex k))  none

notation k " [S]⇉ᵣ∅ " => PointsToS (ProdIndex.right (ChipIndex.sbufUnboundedIndex k)) none
notation k " [P]⇉ᵣ∅ " => PointsToS (ProdIndex.right (ChipIndex.psumUnboundedIndex k)) none
notation k " [H]⇉ᵣ∅ " => PointsToS (ProdIndex.right (ChipIndex.hbmUnboundedIndex k))  none

def wp_F (wp : LeibnizO Nat → Prog DataT → Prog DataT → (Value DataT → Value DataT → PROP DataT) → PROP DataT)
         (K : LeibnizO Nat)
         (p1 p2 : Prog DataT)
         (Φf : Value DataT → Value DataT → PROP DataT) : PROP DataT :=
  -- For any pair of states that satisfy the state interpretation...
  iprop(
      -- Either, that configuration is a value, and the postcondition holds,
      (|==> ∃ vl, ∃ vr, ⌜toVal p1 = some vl⌝ ∗ ⌜toVal p2 = some vr⌝ ∗ Φf vl vr) ∨
      -- Or, they're not values, and for any two configurations that we can step into, in some number of steps,
      ( -- ⌜toVal p1 = none ∨ toVal p2 = none⌝ ∗
        ∀ sl, ∀ sr, state_interp sl sr -∗
        ∃ cl', ∃ cr', ∃ nl, ∃ nr,
          ⌜0 < nl ∧ 0 < nr ∧ nl ≤ K.car ∧ nr ≤ K.car ∧ SmallStep.StepN nl (p1, sl) cl' ∧ SmallStep.StepN nr (p2, sr) cr'⌝ ∗
            -- We can reobtain the state interp for the new state, and also
            -- prove the weakest precondition.
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp K cl'.1 cr'.1 Φf)))

instance wp_contractive : Iris.OFE.Contractive (α := LeibnizO Nat → Prog DataT → Prog DataT → (Value DataT → Value DataT → PROP DataT) → PROP DataT) wp_F := by
  sorry

/-- Definition of the weakest precondition -/
def wp (K : LeibnizO Nat) (p1 p2 : Prog DataT) (Φf : Value DataT → Value DataT → PROP DataT) : PROP DataT :=
  (Iris.fixpoint wp_F) K p1 p2 Φf

theorem wp_unfold {K : LeibnizO Nat} {p1 p2 : Prog DataT} {Φf : Value DataT → Value DataT → PROP DataT} :
    wp K p1 p2 Φf ≡
    iprop(
      (|==> ∃ vl, ∃ vr, ⌜toVal p1 = some vl⌝ ∗ ⌜toVal p2 = some vr⌝ ∗ Φf vl vr) ∨
      ( ∀ sl, ∀ sr, state_interp sl sr -∗
        ∃ cl', ∃ cr', ∃ nl, ∃ nr,
          ⌜0 < nl ∧ 0 < nr ∧ nl ≤ K.car ∧ nr ≤ K.car ∧ SmallStep.StepN nl (p1, sl) cl' ∧ SmallStep.StepN nr (p2, sr) cr'⌝ ∗
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp K cl'.1 cr'.1 Φf))) := by
  apply fixpoint_unfold (f := ⟨wp_F, OFE.ne_of_contractive wp_F⟩)

end weakestpre

theorem wp_to_fupd_PRelS {pl pr : Prog DataT} {sl sr : NML.State DataT}
      {Φf : NML.Value DataT → NML.Value DataT → Prop} {n : Nat} :
    wp K pl pr (fun vl vr => iprop(⌜(Φf vl vr : Prop)⌝)) ⊢
    state_interp sl sr -∗ |==> ▷^[n] ⌜(NML.NMLSemantics DataT).PRelS n K.car (pl, sl) (pr, sr) Φf ⌝ := by
  revert pl pr sl sr
  induction n with | zero => ?_ | succ n IH => ?_
  · -- Base case: n=0 so postcondition is trivial
    intro pl pr sl sr
    istart; iintro H1 H2; iclear H1; iclear H2; istop
    exact Iris.BIUpdate.intro
  · -- Inductive case
    intro pl pr sl sr
    -- Unfold the WP
    apply Iris.BI.BIBase.Entails.trans
    · apply (Iris.BI.equiv_iff.mp wp_unfold).mp.trans
      exact .rfl -- What

    istart
    iintro Hwp Hσ
    -- ispecialize Hwp Hσ
    icases Hwp with ⟨H|H⟩
    · -- Both programs are values
      iclear Hσ
      istop
      -- Strip the update modality
      apply Iris.BIUpdate.mono
      istart
      iintro ⟨vl, vr, %Hvl, %Hvr, %HΦ⟩
      istop

      -- Intro a bunch of laters for a pure prop, this should be OK?
      refine .trans ?_ laterN_intro
      apply Iris.BI.pure_intro
      simp [SmallStep.PRelS, Hvl, Hvr]
      exact HΦ

    · -- Both programs can step
      ispecialize H Hσ
      icases H with ⟨cl', cr', nl, nr, ⟨%Hnl0, %Hnr0, %HnlK, %HnrK, %HSl, %HSr⟩, H⟩
      simp only [Iris.BI.BIBase.laterN]
      istop

      -- Since they both can step, neither of them is a value
      have p1_not_value : (NML.NMLSemantics DataT).toVal pl = none := by
        cases h : (NML.NMLSemantics DataT).toVal pl; trivial
        exfalso
        rcases nl with (_|nl); omega
        rw [Nat.add_comm] at HSl
        obtain ⟨⟨pl', sl'⟩, H, _⟩ := (NML.NMLSemantics DataT).StepN_add_iff.mp HSl
        apply (NML.NMLSemantics DataT).toVal_isSome_isStuck ?_ ((NML.NMLSemantics DataT).step_of_stepN_one H)
        rw [h]; constructor
      have p2_not_value : (NML.NMLSemantics DataT).toVal pr = none := by
        cases h : (NML.NMLSemantics DataT).toVal pr; trivial
        exfalso
        rcases nr with (_|nr); omega
        rw [Nat.add_comm] at HSr
        obtain ⟨⟨pl', sl'⟩, H, _⟩ := (NML.NMLSemantics DataT).StepN_add_iff.mp HSr
        apply (NML.NMLSemantics DataT).toVal_isSome_isStuck ?_ ((NML.NMLSemantics DataT).step_of_stepN_one H)
        rw [h]; constructor

      -- It suffices to get a PRelS for the continuation
      have Hcont : SmallStep.PRelS n K.car cl' cr' Φf → SmallStep.PRelS (n + 1) K.car (pl, sl) (pr, sr) Φf := by
        intro H
        simp only [p1_not_value, p2_not_value, SmallStep.PRelS]
        exists nl; exists nr; exists cl'; exists cr'

      suffices
          Iris.BI.later iprop(|==> (state_interp cl'.snd cr'.snd ∗ wp K cl'.fst cr'.fst fun vl vr => iprop(⌜Φf vl vr⌝))) ⊢
          |==> Iris.BI.later iprop(▷^[n]⌜SmallStep.PRelS n K.car cl' cr' Φf⌝) by
        apply this.trans
        apply Iris.BIUpdate.mono
        apply Iris.BI.later_mono
        exact laterN_mono fun n x a => Hcont
      clear Hcont

      -- Apply the IH

      suffices
        Iris.BI.later iprop(|==> |==> ▷^[n]⌜SmallStep.PRelS n K.car (cl'.1, cl'.2) (cr'.1, cr'.2) Φf⌝ : PROP DataT) ⊢
        |==> Iris.BI.later iprop(▷^[n]⌜SmallStep.PRelS n K.car cl' cr' Φf⌝) by
        refine .trans ?_ this
        refine Iris.BI.later_mono ?_
        refine Iris.BIUpdate.mono ?_
        exact Iris.BI.wand_elim' IH
      clear IH
      simp

      -- Collapse the two bupds
      suffices
          Iris.BI.later iprop(|==> ▷^[n]⌜SmallStep.PRelS n K.car (cl'.fst, cl'.snd) (cr'.fst, cr'.snd) Φf⌝) ⊢
          |==> Iris.BI.later iprop(▷^[n]⌜SmallStep.PRelS n K.car cl' cr' Φf⌝) by
        refine .trans ?_ this
        apply Iris.BI.later_mono
        exact Iris.BIUpdate.trans

      -- Exchange bupd and later
      apply later_bupd_comm_plain


theorem wp_adequacy_pre {pl pr : Prog DataT} {sl sr : NML.State DataT} {Φf : NML.Value DataT → NML.Value DataT → Prop}
    (H : ∀ n, (state_interp sl sr ∗ state_frag sl sr ⊢ |==> ▷^[n] ⌜(NML.NMLSemantics DataT).PRelS n K (pl, sl) (pr, sr) Φf ⌝)) :
    ∀ n, (NML.NMLSemantics DataT).PRelS n K (pl, sl) (pr, sr) Φf := by
  intro n


  -- UPred.ownM <|
  -- UPred.ownM <| ◯V HasHHMap.hhmap (fun (_ : K) (v : V) => some (DFrac.own 1, toAgree <| .mk v)) m

  apply UPred.soundness_pure_gen (A := PROPR DataT) (n := n)
    (a :=
      (●V HasHHMap.hhmap (fun (_ : KLR.Core.ProdNeuronIndex) (v : DataT) => some (Iris.toAgree <| Iris.LeibnizO.mk v))
          (KLR.Core.ProdStore.mk sl.memory sr.memory)) •
      (◯V HasHHMap.hhmap (fun (_ : KLR.Core.ProdNeuronIndex) (v : DataT) => some (Iris.DFrac.own 1, Iris.toAgree <| Iris.LeibnizO.mk v))
          (KLR.Core.ProdStore.mk sl.memory sr.memory : KLR.Core.ProdNeuronMemory _)))
  · refine Iris.CMRA.Valid.validN ?_
    apply View.view_both_valid.mpr
    intro n'
    simp [heapR, Store.all]
    intro k
    simp [toHeapPred, hhmap_get]
    rcases h : (Store.get ({ left := sl.memory, right := sr.memory } : KLR.Core.ProdNeuronMemory _) k) with (_|v)
    · simp
    simp
    exists (Iris.DFrac.own 1)
  apply UPred_adequacy_laterN_gen (N := n)
  · apply View.view_both_valid.mpr
    intro n'
    simp [heapR, Store.all]
    intro k
    simp [toHeapPred, hhmap_get]
    rcases h : (Store.get ({ left := sl.memory, right := sr.memory } : KLR.Core.ProdNeuronMemory _) k) with (_|v)
    · simp
    simp
    exists (Iris.DFrac.own 1)
  apply bupd_gen_soundness
  apply Iris.BI.BIBase.Entails.trans _ (H n)
  -- Combine the ghost state
  exact (UPred.ownM_op _ _).mp


theorem wp_adequacy_no_alloc {pl pr : Prog DataT} {sl sr : NML.State DataT} {Φf : NML.Value DataT → NML.Value DataT → Prop}
    (H : state_frag sl sr ⊢ wp K pl pr (fun vl vr => iprop(⌜(Φf vl vr : Prop)⌝))) :
    (NML.NMLSemantics DataT).PRel (pl, sl) (pr, sr) Φf := by
  apply SmallStep.PrelNLimit (K := K.car)
  intro n
  apply SmallStep.PRelNS n
  apply wp_adequacy_pre
  intro n'
  apply Iris.BI.wand_entails
  suffices
      (wp K pl pr (fun vl vr => iprop(⌜(Φf vl vr : Prop)⌝)) ⊢ state_interp sl sr -∗ |==> ▷^[n']⌜SmallStep.PRelS n' K.car (pl, sl) (pr, sr) Φf⌝) →
      (⊢ state_interp sl sr ∗ state_frag sl sr -∗ |==> ▷^[n']⌜SmallStep.PRelS n' K.car (pl, sl) (pr, sr) Φf⌝) by
    apply this; clear this
    apply wp_to_fupd_PRelS
  intro H
  refine Iris.BI.entails_wand ?_
  apply Iris.BI.BIBase.Entails.trans _ (Iris.BI.wand_elim' H)
  rename_i Hwp
  exact Iris.BI.sep_mono (fun n x a a => a) Hwp

/-- Definition for Hoare Triple -/
def triple (pre : PROP DataT) K (p1 p2 : Prog DataT) post :=
  iprop(pre -∗ wp K p1 p2 post)

macro "{{ " pre:term  " }} " p1:term " × " p2:term "{{ " x:ident  " => " post:term " }} " : term => do
  ``(triple $pre $p1 $p2 (fun $x => $post))
