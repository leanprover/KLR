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

  -- The proof:
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
