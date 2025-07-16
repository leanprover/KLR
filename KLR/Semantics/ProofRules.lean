/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Logic

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML

variable {DataT : Type _}

/-- Value-value rule: base case for the proof -/
theorem wp_val_val {c1 c2 : @prog DataT × @state DataT} {v1 v2 : val} {Φ : val → val → @PROP DataT} {K}
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
