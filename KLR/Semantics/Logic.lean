/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.NML
import KLR.Semantics.Memory
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Instances.UPred
import Iris.Instances.heProp
import Iris.BI.BI

-- The logic: I can reuse UPred with a fixed ghost state (first-order)
-- I'll want the fixpoint combinator to define the wp
-- Need to port some more of the upred rules most likely

section weakestpre
open Iris.BI.BIBase KLR.Core

variable {DataT : Type _}

abbrev prog := (NML.NMLSemantics DataT).Prog
abbrev state := (NML.NMLSemantics DataT).State
abbrev val := (NML.NMLSemantics DataT).Val
abbrev step := (NML.NMLSemantics DataT).Step
abbrev to_val := (NML.NMLSemantics DataT).toVal

abbrev PNat := { n : Nat // 0 < n }

instance : DFractional PNat where
  proper n := n.1 = 1
  add := sorry
  add_comm := sorry
  add_assoc := sorry
  add_left_cancel := sorry
  add_ne := sorry
  proper_add_mono_left := sorry
  one := sorry
  whole_iff_one := sorry

structure ProdChipMemory (T : Type _) where
  left : KLR.Core.ChipMemory T
  right : KLR.Core.ChipMemory T

inductive ProdIndex
| left (_ : KLR.Core.DualMemoryStoreIndex)
| right (_ : KLR.Core.DualMemoryStoreIndex)

instance {T : Type _} : Heap (ProdChipMemory T) ProdIndex T where
  get := sorry
  set := sorry
  of_fun := sorry
  fresh := sorry
  get_set_eq := sorry
  get_set_ne := sorry
  of_fun_get := sorry
  point := sorry
  fresh_get := sorry
  point_get_eq := sorry
  point_get_ne := sorry

def TProd (H : Type _ → Type _) (T : Type _) : Type _ := H T × H T

abbrev PROP : Type _ := heProp PNat ProdIndex (UCell UInt8 DataT) ProdChipMemory

-- The state interpretation, ie the global version of the program state.
def state_interp (l r : @state DataT) : @PROP DataT :=
  heProp_auth _ _ _ _ (.mk l.memory r.memory)
  -- Strong relational invariant goes here?

def wp_F (wp : @prog DataT → @prog DataT → (@val DataT → @val DataT → @PROP DataT) → @PROP DataT)
         (p1 p2 : @prog DataT)
         (Φf : @val DataT → @val DataT → @PROP DataT) : @PROP DataT :=
  -- For any pair of states that satisfy the state interpretation...
  «forall» fun sl : @state DataT =>
  «forall» fun sr : @state DataT =>
    iprop(state_interp sl sr -∗
      -- Either, that configuration is a value, and the postcondition holds,
      (|==>
        «exists» fun vl : @val DataT =>
        «exists» fun vr : @val DataT =>
        iprop(⌜to_val p1 = some vl⌝ ∗ ⌜to_val p2 = some vr⌝ ∗ Φf vl vr)) ∨
      -- Or, for any two configurations that we can step into, in some number of steps,
      ( «forall» fun cl' : @prog DataT × @state DataT =>
        «forall» fun cr' : @prog DataT × @state DataT =>
        «exists» fun nl : Nat =>
        «exists» fun nr : Nat =>
        iprop(
          ⌜(NML.NMLSemantics DataT).StepN nl.succ (p1, sl) cl' ∧
            (NML.NMLSemantics DataT).StepN nr.succ (p2, sr) cr'⌝ -∗
            -- We can reobtain the state interp for the new state, and also
            -- prove the weakest precondition.
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp cl'.1 cr'.1 Φf))))

instance : Iris.OFE.Contractive (α := @prog DataT → @prog DataT → (@val DataT → @val DataT → @PROP DataT) → @PROP DataT) wp_F := by
  sorry

/-- Definition of the weakest precondition -/
def wp (p1 p2 : @prog DataT) (Φf : @val DataT → @val DataT → @PROP DataT) : @PROP DataT :=
  (Iris.fixpoint wp_F) p1 p2 Φf

end weakestpre

/-- If the two terms are values, then we at the very least get a relationship between their values. -/
theorem wp_value_value_fupd {pl pr : @prog DataT} {Φf : @val DataT → @val DataT → Prop}
    (Hpl : (NML.NMLSemantics DataT).IsValue pl) (Hpr : (NML.NMLSemantics DataT).IsValue pr) :
    wp pl pr (fun vl vr => iprop(⌜(Φf vl vr : Prop)⌝)) ⊢
      |==> ⌜∃ (vl vr : @val DataT), to_val pl = some vl ∧ to_val pr = some vr ∧ Φf vl vr⌝ := by
  -- I need internal eq to actually do this unfolding.
  unfold wp
  sorry

/-- Definition for Hoare Triple -/
def triple (pre : @PROP DataT) (p1 p2 : @prog DataT) post :=
  iprop(pre -∗ wp p1 p2 post)

macro "{{ " pre:term  " }} " p1:term " × " p2:term "{{ " x:ident  " => " post:term " }} " : term => do
  ``(triple $pre $p1 $p2 (fun $x => $post))


-- Below: OUTDATED

-- Φf is a proposition on the global state.
-- We prove a family of adequacy theorems for different Φf.
--
-- Define ↦ₜ as "maps to tensor"... LHS is a TensorHandle (specifies handedness + size + location in memory), RHS is a logical tensor.
-- Most general will be something like
--
--    -- Paramaters:
--    (pl pr : Argument → Output → expr) (Φvᵢ Φvₒ Φrᵢ Φrₒ: Tensor → Tensor → Prop) (Φf : Val → Val → Prop)
--    (llᵢ llₒ lrᵢ lrₒ : Locations in HBM) (HD : Disjointness of locations)
--
--    initialMemory : Handedness → HBM Loc → HBM Loc → InTensors → OutTensors → State     -- A state with everything empty, inputs loaded & locations, outputs allocated.
--    initialProp   : Handedness → HBM Loc → HBM Loc → InTensors → OutTensors → PROP DataT      -- Same as initialMemory, but in PROP DataT with ownership using ↦ₜ
--    finalMemory   : Handedness → HBM Loc → HBM Loc → InTensors → OutTensors → State     -- A state with everything empty, inputs loaded & locations, outputs allocated.
--    finalProp     : Handedness → HBM Loc → HBM Loc → InTensors → OutTensors → PROP DataT      -- Same as initialMemory, but in PROP DataT with ownership using ↦ₜ
--
--    -- Precondition: There exist tensors satisfying the inital relations at the right locations.
--    (∃ vlᵢ vlₒ vrᵢ vrₒ,
--        initialProp left  llᵢ llₒ vlᵢ vlₒ ∗
--        initialProp right lrᵢ lrₒ vrᵢ vrₒ ∗
--        ⌜Φvᵢ vlᵢ vrᵢ⌝ ∗
--        ⌜Φvₒ vlₒ vlₒ⌝)
--
--    -∗ wp (pl llᵢ llₒ) (pr lrᵢ lrₒ) (fun vl vr =>
--
--    -- Postcondition: There exist tensors satisfying the final relations at the right locations, and the values satisfy the value relation.
--      ∃ vlᵢ vlₒ vrᵢ vrₒ,
--        finalProp left  llᵢ llₒ vlᵢ vlₒ ∗
--        finalProp right lrᵢ lrₒ vrᵢ vrₒ ∗
--        ⌜Φrᵢ vlᵢ vrᵢ⌝ ∗
--        ⌜Φrₒ vlₒ vlₒ⌝ ∗
--        ⌜Φf vl vr⌝)
--
--
-- Then we eventually (after going through modalities, ∀ n, PRelN n...) get...
--
--    PRel
--      (fun (p1, σₗ) (p2, σᵣ) =>
--        p1 = pl llᵢ llₒ ∧
--        p2 = pr lrᵢ lrₒ ∧
--        ∃ vlᵢ vlₒ vrᵢ vrₒ,
--          initialMemory left  llᵢ llₒ vlᵢ vlₒ ∧
--          initialMemory right lrᵢ lrₒ vrᵢ vrₒ ∧
--          Φvᵢ vlᵢ vrᵢ ∧
--          Φvₒ vlₒ vlₒ)
--      (fun (vₗ, σₗ) (vᵣ, σᵣ) => ∃ vlᵢ vlₒ vrᵢ vrₒ,
--        finalMemory left  llᵢ llₒ vlᵢ vlₒ ∧
--        finalMemory right lrᵢ lrₒ vrᵢ vrₒ ∧
--        Φrᵢ vlᵢ vrᵢ ∧
--        Φrₒ vlₒ vlₒ ∧
--        Φf vl vr)
--
-- Question: I wonder if there's a generic way to do this--to get assertions about the global memory from a heProp.
-- Question: Do I need to add a soundness theorem to heProp to cope with magic wands?

--
-- Adequacy argument planning:
--
-- 1. go from (PRE -∗ wp prog POST) to (state_interp PRE -∗ |==>^n▷^n (PRelN n (pure PRE) (pure POST)))
-- 2. Use heProp soundness theorem
-- 3. Need relationship between PRelN and PRel
--      -> Adequacy should get us ∀ n, PRelN n ...
--         This is Because the programs are eventually constant wrt. the amount of fuel.
