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

macro "dwp_left_pure " t:term : tactic =>
  `(tactic| apply Entails.trans ?_ <| wand_entails <| dwpPureL $t (Hx := by simp))

macro "dwp_right_pure " t:term : tactic =>
  `(tactic| apply Entails.trans ?_ <| wand_entails <| dwpPureR $t (Hx := by simp))

theorem include_sep {P Q : @PROP DataT} (L : ⊢ P) (H : P ∗ Q ⊢ R) : Q ⊢ R := by
  refine Entails.trans ?_ (Q := iprop(P ∗ Q)) ?_
  · refine Entails.trans ?_ (Q := iprop(emp ∗ Q)) ?_
    · exact ProofMode.from_and_intro (fun n x a a => trivial) fun n x a a => a
    · exact sep_mono L fun n x a a => a
  · exact H
