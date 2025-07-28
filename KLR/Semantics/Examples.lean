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
open Iris.BI.BIBase KLR.Core Iris NML

variable {DataT : Type _}

/-- Example relation: Both programs reutrn integers, and the integer of the left program is less
than the integer of the right program. -/

def ΦIsIntLePure (v1 v2 : @val DataT) : Prop := ∃ (z1 z2 : Int), v1 = NML.Value.int z1 ∧ v2 = .int z2 ∧ z1 < z2
def ΦIsIntLe (v1 v2 : @val DataT) : @PROP DataT := iprop(⌜ΦIsIntLePure v1 v2⌝)



/-- Simplest possible example: Two programs in "done" states -/
theorem example0 (σ : @state DataT): ⊢ (@wp DataT ⟨1⟩ (.done (.int 4)) (.done (.int 5)) ΦIsIntLe) := by
  apply Entails.trans ?_ (@wpValVal _ (K := ⟨1⟩) (.done (.int 4), σ) (.done (.int 5), σ) (.int 4) (.int 5) ΦIsIntLe (by rfl) (by rfl))
  istart
  simp only [ΦIsIntLe]
  ipure_intro; exists 4; exists 5

/-- Two "return" programs are related if the values they return are -/
theorem example1 (σ₁ σ₂ : @state DataT) :
  ⊢ (@wp DataT ⟨1⟩
         (.run [⟨.ret (.val (.int 4)), fun _ => .none⟩])
         (.run [⟨.ret (.val (.int 5)), fun _ => .none⟩])
         ΦIsIntLe) := by
  -- Junk needed because bad automation
  let p1 : (NMLSemantics DataT).Prog  := .run [⟨.ret (.val (.int 4)), fun _ => .none⟩]
  let p2 : (NMLSemantics DataT).Prog  := .run [⟨.ret (.val (.int 5)), fun _ => .none⟩]
  let p1' : (NMLSemantics DataT).Prog := .done (.int 4)
  let p2' : (NMLSemantics DataT).Prog := .done (.int 5)
  have RuleInst1 := @wpPureSync DataT p1 p2 p1' p2' ΦIsIntLe ⟨1⟩
       (fun _ => step.ret <| ExprStep.value rfl)
       (fun _ => step.ret <| ExprStep.value rfl)
       (by trivial)
  have RuleInst2 := @wpValVal DataT (p1', σ₁) (p2', σ₂) (.int 4) (.int 5) ΦIsIntLe ⟨1⟩
       (by rfl)
       (by rfl)

  -- The proof
  apply Entails.trans _ RuleInst1
  apply Entails.trans _ RuleInst2
  istart
  simp only [ΦIsIntLe]
  ipure_intro; exists 4; exists 5

/-- A proof that both programs
    - Are safe,
    - Are equiterminating,
    - Step to values related by ΦIsIntLePure if they (both) terminate
-/
theorem example1_full (σ₁ σ₂ : @state DataT) :
  (NMLSemantics DataT).PRel
    ((.run [⟨.ret (.val (.int 4)), fun _ => .none⟩]), σ₁)
    ((.run [⟨.ret (.val (.int 5)), fun _ => .none⟩]), σ₂)
    ΦIsIntLePure := by
  apply wp_adequacy_no_alloc (K := ⟨1⟩)
  istart; iintro H; iclear H; istop
  exact example1 σ₁ σ₂

/-! Example 2: Allocation
This is one of the simplest state-transforming ste
Prove that allocation under any heap is safe using a relational proof.
-/

def ex2 : (NMLSemantics DataT).Prog :=
  (.run [⟨.assign .none (.alloc Memory.sbuf), nolocals _⟩, ⟨.ret <| .val .unit, nolocals _⟩])

theorem example2 (σ : @state DataT) : (NMLSemantics DataT).Safe (ex2, σ) := by
  -- It suffices to show that `(ex2, σ) ∼ (ex2, σ) : fun _ _ => True`
  apply SmallStep.Safe_of_PRel (Φf := fun _ _ => True)
  -- Enter the Iris proof
  apply wp_adequacy_no_alloc (K := ⟨1⟩)
  unfold ex2
  sorry


-- Testing desynced stepping


-- TODO: Generalize: Assignment of a _pure expression_ to a variable
-- is a pure step which adds the pure variable to the local context
/-- Assignment of a value to none is Pure -/
theorem AssignValuePure (v : (NMLSemantics DataT).Val) :
    PureStep (.run <| ⟨.assign .none (.val v), loc⟩ :: p') (.run p') :=
  fun _ => step.seq <| .value rfl


def ΦUnitEq (v1 v2 : @val DataT) : @PROP DataT := iprop(⌜v1 = .unit ∧ v2 = .unit⌝)

def e3L : (NMLSemantics DataT).Prog :=
  .run [
    ⟨.assign .none (.val (.int 3)), nolocals _⟩,
    ⟨.assign .none (.val (.bool false)), nolocals _⟩,
    ⟨.assign .none (.val .unit), nolocals _⟩,
    ⟨.assign .none (.val (.int 3)), nolocals _⟩,
    ⟨.ret (.val .unit), nolocals _⟩,
  ]

def e3R : (NMLSemantics DataT).Prog :=
  .run [
    ⟨.assign .none (.val .unit), nolocals _⟩,
    ⟨.assign .none (.val (.bool false)), nolocals _⟩,
    ⟨.ret (.val .unit), nolocals _⟩,
  ]

--  TODO: use iapply
theorem e3 : ⊢ @wp DataT ⟨2⟩ e3L e3R ΦUnitEq := by
  -- Enter desync mode
  apply Entails.trans ?_ (BI.wand_entails <| wpDesync ΦUnitEq)

  -- Left pure step
  apply Entails.trans ?_ (BI.wand_entails <| awpPureL (AssignValuePure _) (Hx := by simp))
  -- Left pure step
  apply Entails.trans ?_ (BI.wand_entails <| awpPureL (AssignValuePure _) (Hx := by simp))
  -- Note how a third pure step doesn't work here becase we're proving a wp with ⟨2⟩ stuttering
  -- apply Entails.trans ?_ (BI.wand_entails <| awpPureL (AssignValuePure _) (Hx := by simp))

  -- Right pure step
  apply Entails.trans ?_ (BI.wand_entails <| awpPureR (AssignValuePure _) (Hx := by simp))
  simp only [Nat.sub_self, Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.add_one_sub_one]

  -- Resync
  apply Entails.trans ?_ (BI.wand_entails <| wpResync _)

  -- Now we can do another batch of desync steps
  apply Entails.trans ?_ (BI.wand_entails <| wpDesync _)
  apply Entails.trans ?_ (BI.wand_entails <| awpPureL (AssignValuePure _) (Hx := by simp))
  apply Entails.trans ?_ (BI.wand_entails <| awpPureL (AssignValuePure _) (Hx := by simp))
  apply Entails.trans ?_ (BI.wand_entails <| awpPureR (AssignValuePure _) (Hx := by simp))
  apply Entails.trans ?_ (BI.wand_entails <| wpResync _)

  -- Then it's the same as above (FIXME: Refactor)
  have RuleInst1 :=
    @wpPureSync DataT
      (.run [⟨.ret (.val .unit), nolocals _⟩]) (.run [⟨.ret (.val .unit), nolocals _⟩])
      (.done .unit) (.done .unit)
      ΦUnitEq ⟨2⟩
      (fun _ => step.ret <| ExprStep.value rfl)
      (fun _ => step.ret <| ExprStep.value rfl)
      (by trivial)
  apply Entails.trans ?_ RuleInst1; clear RuleInst1

  have σ₁ : @state DataT := sorry
  have σ₂ : @state DataT := sorry

  -- Fix this rule to not need states
  have RuleInst2 := @wpValVal DataT ((ExecState.done Value.unit), σ₁) ((ExecState.done Value.unit), σ₂) .unit .unit
       ΦUnitEq ⟨2⟩
       (by rfl)
       (by rfl)
  simp only [] at RuleInst2
  apply Entails.trans ?_ RuleInst2; clear RuleInst2
  simp [ΦUnitEq]
  exact BI.true_intro



-- Other things I need to test soon:
-- Assignments to variables
-- Starting with state in hbm

def e4L : (NMLSemantics DataT).Prog :=
  .run [⟨.assign (.some "x") (.val <| .int 3), nolocals _⟩, ⟨.ret (.var "x"), nolocals _⟩]

def e4R : (NMLSemantics DataT).Prog :=
  .run [⟨.assign (.some "y") (.val <| .int 3), nolocals _⟩, ⟨.ret (.var "y"), nolocals _⟩]


def ΦInt (R : Int → Int → @PROP DataT) (v1 v2 : @val DataT) : @PROP DataT :=
  iprop(∃ z1 z2, ⌜v1 = .int z1⌝ ∗ ⌜v2 = .int z2⌝ ∗ R z1 z2)
def ΦIntPure (R : Int → Int → Prop) (v1 v2 : @val DataT) : @PROP DataT :=
  ΦInt (fun z1 z2 => (iprop(⌜R z1 z2⌝) : @PROP DataT)) v1 v2

theorem e4 : ⊢ (@wp DataT ⟨1⟩ e4L e4R (ΦIntPure (· = ·))) := by
  unfold e4L e4R
  -- I really need this independent stepping thing
  sorry


-- Idea: Iterator as value (make the proof rule use Lob induction)
