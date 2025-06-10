/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.NML
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Instances.UPred

-- The logic: I can reuse UPred with a fixed ghost state (first-order)
-- I'll want the fixpoint combinator to define the wp
-- Need to port some more of the upred rules most likely


section logic_test
open Iris NML Iris.BI.BIBase Lean

variable {Heap : Type _} [UCMRA Heap] {DataT : Type _}

abbrev PROP := UPred Heap

-- Agreement over the NKI heaps
-- TODO:
def state_interp : State × State → UPred Heap := sorry

-- The relation that defines the product steps we can take
def PREL : Cfg × Cfg → (Cfg × Cfg → UPred Heap) → UPred Heap :=
  sorry

-- A standard Iris WP
-- Note: Iris-lean → is Iris -d> by default
-- TODO: Lift to products
def wp_F (wp : Pgm × Pgm → (@Value DataT × @Value DataT → UPred Heap) → UPred Heap)
    (p : Pgm × Pgm) (Φ : @Value DataT × @Value DataT → UPred Heap) : UPred Heap :=
  «forall» fun sl : State =>
  «forall» fun sr : State =>
  -- TODO: Merge update syntax into iris-lean main brainc
  iprop(state_interp (sl, sr) -∗ PREL ((p.1, sl), (p.2, sr))
    (fun ((pl', sl'), (pr', sr')) => iprop(▷ (state_interp (sl', sr') ∗ wp (pl', pr') Φ))))

def wp (p : Pgm × Pgm) (Φ : @Value DataT × @Value DataT → UPred Heap) : UPred Heap :=
  -- Port: The fixpoint theorem we skipped to close over wp_F
  sorry

def triple (pre : UPred Heap) (p1 p2 : Pgm) (post : @Value DataT × @Value DataT → UPred Heap) :=
  iprop(pre -∗ wp (p1, p2) post)

macro "{{ " pre:term  " }} " p1:term " × " p2:term "{{ " x:ident  " => " post:term " }} " : term => do
  ``(triple $pre $p1 $p2 (fun $x => $post))

end logic_test
