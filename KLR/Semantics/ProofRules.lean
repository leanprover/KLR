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
