/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.NML
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Instances.UPred
import Iris.Instances.heProp
import Iris.BI.BI

-- The logic: I can reuse UPred with a fixed ghost state (first-order)
-- I'll want the fixpoint combinator to define the wp
-- Need to port some more of the upred rules most likely

section weakestpre
open Iris.BI.BIBase

variable {DataT : Type _}


abbrev prog := (NML.NMLSemantics DataT).prog
abbrev state := (NML.NMLSemantics DataT).state
abbrev val := (NML.NMLSemantics DataT).val
abbrev step := (NML.NMLSemantics DataT).step
abbrev to_val := (NML.NMLSemantics DataT).to_val

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

abbrev PROP : Type _ := heProp PNat ProdIndex UInt8 ProdChipMemory

-- The state interpretation, ie the global version of the program state.
def state_interp (l r : @state DataT) : PROP :=
  heProp_auth _ _ _ _ (.mk l.memory r.memory)
  -- Strong relational invariant goes here?

def wp_F (wp : @prog DataT → @prog DataT → (@val DataT → @val DataT→ PROP) → PROP)
         (p1 p2 : @prog DataT)
         (Φf : @val DataT → @val DataT → PROP) : PROP :=
  -- For any pair of states that satisfy the state interpretation...
  «forall» fun sl : @state DataT =>
  «forall» fun sr : @state DataT =>
    iprop(state_interp sl sr -∗
      -- Either, that configuration is a value, and the postcondition holds,
      (|==>
        «exists» fun vl : @val DataT =>
        «exists» fun vr : @val DataT =>
        iprop(⌜to_val (p1, sl) = some vl⌝ ∗ ⌜to_val (p2, sr) = some vr⌝ ∗ Φf vl vr)) ∨
      -- Or, for any two configurations that we can step into, in some number of steps,
      ( «forall» fun cl' : @prog DataT × @state DataT =>
        «forall» fun cr' : @prog DataT × @state DataT =>
        «exists» fun nl : Nat =>
        «exists» fun nr : Nat =>
        iprop(
          ⌜(NML.NMLSemantics DataT).stepN nl.succ (p1, sl) cl' ∧
            (NML.NMLSemantics DataT).stepN nr.succ (p2, sr) cr'⌝ -∗
            -- We can reobtain the state interp for the new state, and also
            -- prove the weakest precondition.
            ▷ |==> (state_interp cl'.2 cr'.2 ∗ wp cl'.1 cr'.1 Φf))))

instance : Iris.OFE.Contractive (α := @prog DataT → @prog DataT → (@val DataT → @val DataT → PROP) → PROP) wp_F := by
  sorry

/-- Definition of the weakest precondition -/
def wp (p1 p2 : @prog DataT) (Φf : @val DataT → @val DataT → PROP) : PROP :=
  (Iris.fixpoint wp_F) p1 p2 Φf

end weakestpre

-- TODO: I really do want values to only be dependent on the expression.
-- Stuckness can still depend on the state (I think that's what I wanted anyways?) but
-- generalizing to values in the cfg is very hard.
-- To get the specs I want (ie. about the final state) I'll need a more souped up adequacy theorem.
-- Namely, I'll want an adequacy theorem that can also talk about the memory in the strong relational
-- invariant.
theorem wp_value_value_fupd {pl pr : @prog DataT} (Φf : @val DataT → @val DataT → PROP) :
  (⊢ wp pl pr Φf) → ⊢ (True : PROP)
  := sorry




/-- Definition for Hoare Triple -/
def triple (pre : PROP) (p1 p2 : @prog DataT) (post : @val DataT → @val DataT → PROP) :=
  iprop(pre -∗ wp p1 p2 post)

macro "{{ " pre:term  " }} " p1:term " × " p2:term "{{ " x:ident  " => " post:term " }} " : term => do
  ``(triple $pre $p1 $p2 (fun $x => $post))
