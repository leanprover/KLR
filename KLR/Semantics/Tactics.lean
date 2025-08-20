/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Logic
import KLR.Semantics.SmallStep
import KLR.Semantics.ProofRules


open Iris.BI.BIBase KLR.Core Iris NML Iris.BI

macro "wp_sync_pure " t1:term ", " t2:term : tactic =>
  `(tactic| refine Entails.trans ?_ <| wpPureSync $t1 $t2 (by simp))

macro "wp_sync_val" : tactic =>
  `(tactic| refine Entails.trans ?_ <| wpValVal (by rfl) (by rfl))

macro "wp_desync" : tactic =>
  `(tactic| refine Entails.trans ?_ <| wand_entails <| wpDesync)

macro "wp_resync" : tactic =>
  `(tactic| refine Entails.trans ?_ <| wand_entails <| wpResync)

-- macro "dwp_left_pure " t:term : tactic =>
--   `(tactic| apply Entails.trans ?_ <| wand_entails <| dwpPureL $t (Hx := by simp))
--
-- macro "dwp_right_pure " t:term : tactic =>
--   `(tactic| apply Entails.trans ?_ <| wand_entails <| dwpPureR $t (Hx := by simp))

theorem tac_uwp_elim_triv_both {P Q : @PROP DataT} (H : P ⊢ Q) : P ⊢ emp ∗ (emp -∗ Q) := by
  apply H.trans
  iintro H
  isplit r
  · exact fun n x a a => a
  iintro -
  iexact H

theorem tac_uwp_elim_triv_pre {P Q R : @PROP DataT} (H : P ⊢ R ∗ Q) : P ⊢ R ∗ (emp -∗ Q) := by
  apply H.trans
  iintro ⟨HR, HQ⟩
  isplit l [HR]
  · iexact HR
  iintro -
  iexact HQ

theorem tac_uwp_elim_triv_post {P Q : @PROP DataT} (H : P ⊢ R -∗ Q) : P ⊢ emp ∗ (R -∗ Q) := by
  apply H.trans
  iintro H
  isplit r [H]
  · exact fun n x a a => a
  iexact H

macro "uwp_left " u:term : tactic => `(tactic|
  apply Entails.trans ?_ (dwpL $u ?_) <;>
  try simp <;>
  (first
   | apply tac_uwp_elim_triv_both
   | apply tac_uwp_elim_triv_pre
   | apply tac_uwp_elim_triv_post
   | skip) <;>
  istart)

macro "uwp_right " u:term : tactic => `(tactic|
  apply Entails.trans ?_ (dwpR $u (by simp)) <;>
  try simp <;>
  (first
   | apply tac_uwp_elim_triv_both
   | apply tac_uwp_elim_triv_pre
   | apply tac_uwp_elim_triv_post
   | skip) <;>
  istart)

macro "dwp_left " u:term : tactic => `(tactic|
  apply Entails.trans ?_ $u <;>
  simp <;>
  (first
   | apply tac_uwp_elim_triv_both
   | apply tac_uwp_elim_triv_pre
   | apply tac_uwp_elim_triv_post
   | skip) <;>
  istart)

macro "dwp_right " u:term : tactic => `(tactic|
  apply Entails.trans ?_ $u <;>
  simp <;>
  (first
   | apply tac_uwp_elim_triv_both
   | apply tac_uwp_elim_triv_pre
   | apply tac_uwp_elim_triv_post
   | skip) <;>
  istart)
