/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Memory
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Instances.UPred
import Iris.Instances.heProp
import Iris.BI
import Iris.ProofMode
import Iris.BI.DerivedLaws

-- The logic: I can reuse UPred with a fixed ghost state (first-order)
-- I'll want the fixpoint combinator to define the wp
-- Need to port some more of the upred rules most likely

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML

variable {DataT : Type _}

abbrev prog := (NML.NMLSemantics DataT).Prog
abbrev state := (NML.NMLSemantics DataT).State
abbrev val := (NML.NMLSemantics DataT).Val
abbrev step := (NML.NMLSemantics DataT).Step
abbrev to_val := (NML.NMLSemantics DataT).toVal
abbrev StepN := (NML.NMLSemantics DataT).StepN

abbrev PROP : Type _ := heProp PNat ProdIndex (UCell UInt8 DataT) ProdChipMemory

-- The state interpretation, ie the global version of the program state.
def state_interp (left right : @state DataT) : @PROP DataT :=
  heProp_auth _ _ _ _ (.mk left.memory right.memory)

def wp_F (wp : @prog DataT → @prog DataT → (@val DataT → @val DataT → @PROP DataT) → @PROP DataT)
         (p1 p2 : @prog DataT)
         (Φf : @val DataT → @val DataT → @PROP DataT) : @PROP DataT :=
  -- For any pair of states that satisfy the state interpretation...
  iprop(∀ sl, ∀ sr, state_interp sl sr -∗
      -- Either, that configuration is a value, and the postcondition holds,
      (|==> ∃ vl, ∃ vr, ⌜to_val p1 = some vl⌝ ∗ ⌜to_val p2 = some vr⌝ ∗ Φf vl vr) ∨
      -- Or, they're not values, and for any two configurations that we can step into, in some number of steps,
      ( ⌜to_val p1 = none ∨ to_val p2 = none⌝ ∗
        ∀ cl', ∀ cr', ∀ nl, ∀ nr,
          ⌜StepN (Nat.succ nl) (p1, sl) cl' ∧ StepN (Nat.succ nr) (p2, sr) cr'⌝ -∗
            -- We can reobtain the state interp for the new state, and also
            -- prove the weakest precondition.
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp cl'.1 cr'.1 Φf)))

instance wp_contractive : Iris.OFE.Contractive (α := @prog DataT → @prog DataT → (@val DataT → @val DataT → @PROP DataT) → @PROP DataT) wp_F := by
  sorry

/-- Definition of the weakest precondition -/
def wp (p1 p2 : @prog DataT) (Φf : @val DataT → @val DataT → @PROP DataT) : @PROP DataT :=
  (Iris.fixpoint wp_F) p1 p2 Φf

theorem wp_unfold {p1 p2 : @prog DataT} {Φf : @val DataT → @val DataT → @PROP DataT} :
    wp p1 p2 Φf ≡
    iprop(∀ sl, ∀ sr, state_interp sl sr -∗
      (|==> ∃ vl, ∃ vr, ⌜to_val p1 = some vl⌝ ∗ ⌜to_val p2 = some vr⌝ ∗ Φf vl vr) ∨
      ( ⌜to_val p1 = none ∨ to_val p2 = none⌝ ∗
        ∀ cl', ∀ cr', ∀ nl, ∀ nr,
          ⌜StepN (Nat.succ nl) (p1, sl) cl' ∧ StepN (Nat.succ nr) (p2, sr) cr'⌝ -∗
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp cl'.1 cr'.1 Φf))) := by
  apply fixpoint_unfold (f := ⟨wp_F, OFE.ne_of_contractive wp_F⟩)

end weakestpre

/-- If the two terms are values, then we at the very least get a relationship between their values. -/
theorem wp_value_value_fupd {pl pr : @prog DataT} {sl sr : @state DataT} {Φf : @val DataT → @val DataT → Prop}
    (Hpl : (NML.NMLSemantics DataT).IsValue pl) (Hpr : (NML.NMLSemantics DataT).IsValue pr) :
    state_interp sl sr ∗ wp pl pr (fun vl vr => iprop(⌜(Φf vl vr : Prop)⌝)) ⊢
            |==> ⌜∃ (vl vr : @val DataT), to_val pl = some vl ∧ to_val pr = some vr ∧ Φf vl vr⌝ := by
  apply Iris.BI.entails_trans.trans (Iris.BI.equiv_iff.mp (Iris.BI.sep_ne.eqv .rfl wp_unfold)).mp
  istart
  iintro ⟨Hs, Hwp⟩
  ispecialize Hwp Hs
  istop
  apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
  istart
  iintro (Hv|⟨⌜Hk⌝, _⟩)
  · istop
    apply Iris.BIUpdate.mono _
    istart
    iintro ⟨vl, vr, ⌜Hvl⌝, ⌜Hvr⌝⟩
    ipure_intro
    exists vl
    exists vr
  · exfalso
    unfold to_val at *
    unfold SmallStep.IsValue at *
    rcases Hk with (Hk | Hk)
    · rw [Hk] at Hpl; cases Hpl
    · rw [Hk] at Hpr; cases Hpr


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
