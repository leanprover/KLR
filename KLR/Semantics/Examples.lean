/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib
import KLR.Semantics.NML
import KLR.Semantics.Logic
import KLR.Semantics.ProofRules
import Iris.ProofMode.Tactics

section weakestpre
open Iris.BI.BIBase KLR.Core Iris NML Iris.BI

variable {DataT : Type _}

/-- Example relation: Both programs reutrn integers, and the integer of the left program is less
than the integer of the right program. -/

def ΦIsIntLePure (v1 v2 : NML.Value DataT) : Prop := ∃ (z1 z2 : Int), v1 = NML.Value.int z1 ∧ v2 = .int z2 ∧ z1 < z2
def ΦIsIntLe (v1 v2 : NML.Value DataT) : @PROP DataT := iprop(⌜ΦIsIntLePure v1 v2⌝)



/-- Simplest possible example: Two programs in "done" states -/
theorem example0 : ⊢ (@wp DataT ⟨1⟩ (.done (.int 4)) (.done (.int 5)) ΦIsIntLe) := by
  apply Entails.trans ?_ (@wpValVal _ (K := ⟨1⟩) (.done (.int 4)) (.done (.int 5)) (.int 4) (.int 5) ΦIsIntLe (by rfl) (by rfl))
  istart
  simp only [ΦIsIntLe]
  ipure_intro; exists 4; exists 5

/-- Two "return" programs are related if the values they return are -/
theorem example1 :
  ⊢ (@wp DataT ⟨1⟩
         (.run [⟨.ret (.val (.int 4)), fun _ => .none⟩])
         (.run [⟨.ret (.val (.int 5)), fun _ => .none⟩])
         ΦIsIntLe) := by
  istart
  apply Entails.trans ?_ <| wpPureSync (RetPure _ _) (RetPure _ _) (by simp)
  apply Entails.trans ?_ <| wpValVal (by rfl) (by rfl)
  simp only [ΦIsIntLe]
  ipure_intro; exists 4; exists 5

/-- A proof that both programs
    - Are safe,
    - Are equiterminating,
    - Step to values related by ΦIsIntLePure if they (both) terminate
-/
theorem example1_full (σ₁ σ₂ : State DataT) :
  (NMLSemantics DataT).PRel
    ((.run [⟨.ret (.val (.int 4)), fun _ => .none⟩]), σ₁)
    ((.run [⟨.ret (.val (.int 5)), fun _ => .none⟩]), σ₂)
    ΦIsIntLePure := by
  apply wp_adequacy_no_alloc (K := ⟨1⟩)
  istart; iintro H; iclear H; istop
  exact example1

/-! Example 2: Allocation
This is one of the simplest state-transforming ste
Prove that allocation under any heap is safe using a relational proof.
-/

def ex2 : ExecState DataT :=
  (.run [⟨.assign .none (.alloc Memory.sbuf), nolocals _⟩, ⟨.ret <| .val .unit, nolocals _⟩])

theorem example2 (σ : State DataT) : SmallStep.Safe (ex2, σ) := by
  -- It suffices to show that `(ex2, σ) ∼ (ex2, σ) : fun _ _ => True`
  apply SmallStep.Safe_of_PRel (Φf := fun _ _ => True)
  -- Enter the Iris proof
  apply wp_adequacy_no_alloc (K := ⟨1⟩)
  unfold ex2
  sorry


-- Testing desynced stepping


def ΦUnitEq (v1 v2 : NML.Value DataT) : @PROP DataT := iprop(⌜v1 = .unit ∧ v2 = .unit⌝)

def e3L : ExecState DataT :=
  .run [
    ⟨.assign .none (.val (.int 3)), nolocals _⟩,
    ⟨.assign .none (.val (.bool false)), nolocals _⟩,
    ⟨.assign .none (.val .unit), nolocals _⟩,
    ⟨.assign .none (.val (.int 3)), nolocals _⟩,
    ⟨.ret (.val .unit), nolocals _⟩,
  ]

def e3R : ExecState DataT :=
  .run [
    ⟨.assign .none (.val .unit), nolocals _⟩,
    ⟨.assign .none (.val (.bool false)), nolocals _⟩,
    ⟨.ret (.val .unit), nolocals _⟩,
  ]

-- #check Entails.trans

--  TODO: use iapply
theorem e3 : ⊢ @wp DataT ⟨2⟩ e3L e3R ΦUnitEq := by
  istart
  -- Enter desync mode, do two left pure steps, and one right pure step. Resync.
  -- Note (commented) that a third pure step does not work becase of the ⟨2⟩ bound.
  apply Entails.trans ?_ <| wand_entails <| wpDesync ΦUnitEq
  apply Entails.trans ?_ <| wand_entails <| awpPureL (AssignValuePure _ _) (Hx := by simp)
  apply Entails.trans ?_ <| wand_entails <| awpPureL (AssignValuePure _ _) (Hx := by simp)
  apply Entails.trans ?_ <| wand_entails <| awpPureR (AssignValuePure _ _) (Hx := by simp)
  -- apply Entails.trans ?_ <| wand_entails <| awpPureL (AssignValuePure _ _) (Hx := by simp)
  apply Entails.trans ?_ <| wand_entails <| wpResync _

  -- Do another batch of desync steps
  apply Entails.trans ?_ <| wand_entails <| wpDesync ΦUnitEq
  apply Entails.trans ?_ <| wand_entails <| awpPureL (AssignValuePure _ _) (Hx := by simp)
  apply Entails.trans ?_ <| wand_entails <| awpPureL (AssignValuePure _ _) (Hx := by simp)
  apply Entails.trans ?_ <| wand_entails <| awpPureR (AssignValuePure _ _) (Hx := by simp)
  apply Entails.trans ?_ <| wand_entails <| wpResync _

  -- And close the proof off like example 1
  apply Entails.trans ?_ <| wpPureSync (RetPure _ _) (RetPure _ _) (by simp)
  apply Entails.trans ?_ <| wpValVal (by rfl) (by rfl)
  simp [ΦUnitEq]
  exact BI.true_intro



-- Other things I need to test soon:
-- Assignments to variables
-- Starting with state in hbm

def e4L : ExecState DataT :=
  .run [⟨.assign (.some "x") (.val <| .int 3), nolocals _⟩, ⟨.ret (.var "x"), nolocals _⟩]

def e4R : ExecState DataT :=
  .run [⟨.assign (.some "y") (.val <| .int 3), nolocals _⟩, ⟨.ret (.var "y"), nolocals _⟩]


def ΦInt (R : Int → Int → @PROP DataT) (v1 v2 : NML.Value DataT) : @PROP DataT :=
  iprop(∃ z1 z2, ⌜v1 = .int z1⌝ ∗ ⌜v2 = .int z2⌝ ∗ R z1 z2)
def ΦIntPure (R : Int → Int → Prop) (v1 v2 : NML.Value DataT) : @PROP DataT :=
  ΦInt (fun z1 z2 => (iprop(⌜R z1 z2⌝) : @PROP DataT)) v1 v2

theorem e4 : ⊢ (@wp DataT ⟨1⟩ e4L e4R (ΦIntPure (· = ·))) := by
  unfold e4L e4R
  -- I really need this independent stepping thing
  sorry


-- Idea: Iterator as value (make the proof rule use Lob induction)
