/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Std.Data.HashMap

/- # Mechanization of a generic nondeterministic small-step semantics -/

structure SmallStep : Type _ where
  prog : Type _
  state : Type _
  val : Type _
  step : prog × state → prog × state → Prop
  to_val : prog × state → Option val
  value_stuck {c c' : prog × state} : (to_val c).isSome → step c c' → False

class SmallStepDet (S : SmallStep) where
  step_det c : ∃ c', ∀ c'', S.step c c'' → c'' = c'

namespace SmallStep

section basic
variable (S : SmallStep)

def stuck (c : S.prog × S.state) : Prop := ∀ c', ¬ S.step c c'

inductive stepN : Nat → S.prog × S.state → S.prog × S.state → Prop where
| done : c = c' → stepN 0 c c'
| step : S.step c c' → stepN n c' c'' → stepN n.succ c c''

theorem stepN_zero_inv (H : S.stepN 0 c c') : c = c' := by cases H; trivial

theorem stepN_stuck_inv (H : S.stepN m c c') (Hs : S.stuck c) : m = 0 := by
  cases H
  · rfl
  · rename_i Hstep HstepN
    exact (Hs _ Hstep).elim

/-- For any of the first n steps of execution, all stuck states satisfy `Φ`. -/
inductive satisfiesN (Φ : S.prog × S.state → Prop) : Nat → S.prog × S.state → Prop where
| stuck : S.stuck c → Φ c → satisfiesN Φ n c
| step  : S.step c c' → satisfiesN Φ n c' → satisfiesN Φ n.succ c

/-
theorem satisfiesN_stepN (H : S.satisfiesN Φ n c) : ∀ m, m ≤ n → S.stuck c' → S.stepN m c c' → Φ c' := by
  revert c
  induction n
  · intro c H m Hm Hs Hs'
    rw [Nat.le_zero_eq] at Hm
    rcases H with ⟨_, H⟩
    exact (stepN_zero_inv S (Hm▸Hs'))▸H
  rename_i n IH
  rintro c H m Hm Hstuck Hstep
  cases H
  · rename_i Hs' HΦ
    have Hz := stepN_stuck_inv S Hstep Hs'
    have Hc := stepN_zero_inv S (Hz ▸ Hstep)
    exact Hc ▸ HΦ
  rename_i _ Hsat Hstep'
  rcases m with (_|m)
  · exact Hstuck _ (stepN_zero_inv S Hstep ▸ Hstep') |>.elim
  -- have Hm' := Nat.add_le_add_iff_right ▸ Hm
  cases Hstep
  -- apply IH Hsat _ (Nat.le_of_lt_succ Hm) Hstuck
  sorry
-/

theorem stepN_1_iff_step : S.stepN 1 (p, s) (p', s') ↔ S.step (p, s) (p', s') := by
  refine ⟨?_, (stepN.step · (stepN.done rfl))⟩
  rintro (_|⟨H,He|_⟩)
  exact He▸H

theorem step_not_stuck (H : S.step (p1, s1) (p1', s1')) : (S.to_val (p1, s1)).isNone := by
  have H' : ¬(S.to_val (p1, s1)).isSome → (S.to_val (p1, s1)).isNone := by
    cases S.to_val (p1, s1) <;> simp
  exact H' (S.value_stuck · H)

end basic

@[simp] abbrev prod.prog (S : SmallStep) := S.prog × S.prog
@[simp] abbrev prod.state (S : SmallStep) := S.state × S.state
@[simp] abbrev prod.val (S : SmallStep) := S.val × S.val

inductive prod.step {S : SmallStep} : (prod.prog S) × (prod.state S) → (prod.prog S) × (prod.state S) → Prop where
| step_l : S.step (p1, s1) (p1', s1') → prod.step ((p1, p2), (s1, s2)) ((p1, p2'), (s1, s2'))
| step_r : S.step (p2, s2) (p2', s2') → prod.step ((p1, p2), (s1, s2)) ((p1, p2'), (s1, s2'))

@[simp] def prod.to_val {S : SmallStep} (c : prod.prog S × prod.state S) : Option (prod.val S) :=
  match S.to_val ⟨c.1.1, c.2.1⟩, S.to_val ⟨c.1.2, c.2.2⟩ with
  | some v1, some v2 => some (v1, v2)
  | _, _ => none

theorem prod.value_stuck {S : SmallStep} {c c' : prod.prog S × prod.state S} :
    (prod.to_val c).isSome → prod.step c c' → False := by
  rcases c with ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
  simp only [to_val]
  split
  · rename_i Hv1 Hv2
    intro _ Hstep; rcases Hstep with (Hs|Hs)
    · exact S.value_stuck (Hv1▸rfl) Hs
    · exact S.value_stuck (Hv2▸rfl) Hs
  · simp

def prod (S : SmallStep) : SmallStep where
  prog := prod.prog S
  state := prod.state S
  val := prod.val S
  step := prod.step
  to_val := prod.to_val
  value_stuck := prod.value_stuck

/-

-- There is a better way


section prod

variable {S : SmallStep}


/-- Every n-step trace in the product semantics can be thought of as two traces in the semantics
of the components. -/
theorem prod.step_noninterference {n : Nat} :
    S.prod.stepN n ((p, q), (s, t)) ((p', q'), (s', t')) ↔
    (∃ mₗ mᵣ : Nat, n = mₗ + mᵣ ∧ S.stepN mₗ (p, s) (p', s') ∧ S.stepN mᵣ (q, t) (q', t')) :=
  sorry

def prod.π₁ (s : S.prod.prog × S.prod.state) : S.prog × S.state := ⟨s.1.1, s.2.1⟩
def prod.π₂ (s : S.prod.prog × S.prod.state) : S.prog × S.state := ⟨s.1.2, s.2.2⟩
def prod.mk (sₗ sᵣ : S.prog × S.state) : S.prod.prog × S.prod.state := ⟨⟨sₗ.1, sᵣ.1⟩, ⟨sₗ.2, sᵣ.2⟩⟩

/-- Relational soundness of the product semantics: If every stuck product trace of at most (2n) steps
satisfies Φ, then for every pair of stuck traces of at most n steps, the relation holds on their stuck values. -/
theorem prod.satisfies_soundness_fin {n : Nat} :
    S.prod.satisfiesN Φ (n + n) c →
    ∀ mₗ mᵣ cₗ cᵣ,
      mₗ < n → mᵣ < n →
      S.stuck cₗ → S.stuck cᵣ →
      S.stepN mₗ (prod.π₁ c) cₗ → S.stepN mₗ (prod.π₂ c) cᵣ →
      Φ (prod.mk cₗ cᵣ) :=
  sorry

end prod
-/


/-- All traces of a configuration do not terminate. -/
def nonterminating {S : SmallStep} (c : S.prog × S.state) : Prop :=
  -- The program never gets stuck
  ∀ n c', S.stepN n c c' → ¬ S.stuck c'

/-- A conservative definition of program equivalence, which should work as long as our semantics
is deterministic. -/
def PRel {S : SmallStep}
    (Φi : (S.prog × S.state) → (S.prog × S.state) → Prop)
    (Φf : S.val → S.val → Prop) : Prop :=
  -- For all starting configurations that are related by Φi,
  ∀ c1 c2, Φi c1 c2 →
  -- They are equiterminating,
  (nonterminating c1 ↔ nonterminating c2) ∧
  -- and for any two finite executions,
  (∀ c1' c2' n m,
    (S.stepN n c1 c1' ∧ S.stuck c1' ∧ S.stepN m c2 c2' ∧ S.stuck c2') →
    -- They only ever get stuck in value states that are related by Φf
    (∃ v1 v2, S.to_val c1' = some v1 ∧ S.to_val c2' = some v2 ∧ Φf v1 v2))



namespace SmallStep


/-
theorem stepExactN_succ_some {n : Nat} (H : stepExactN Pgm State Val n.succ (p2', s2') (p2, s2)) :
    (SmallStep.to_value (Val := Val) (p2', s2')).isNone := by
  rcases H with (_|_)
  suffices ¬(SmallStep.to_value (Val := Val) (p2', s2')).isSome by
    generalize HX : (SmallStep.to_value (Val := Val) (p2', s2')) = X
    rw [HX] at this
    cases X <;> simp_all
  intro H
  apply (SmallStep.value_stuck H)
  rename_i c _ _; exists c

/- A program terminates in a given configuration in at most n steps -/
inductive stepTerm : Nat → Pgm × State → Pgm × State → Prop where
| stepTerm_term : stuck Pgm State Val c → stepTerm n c c
| stepTerm_run : SmallStep.step Val c c' → stepTerm n c' c'' → stepTerm n.succ c c''


def is_value? (c : Pgm × State) : Prop := ¬ (SmallStep.to_value (Val := Val) c) = .none

/-- For the first n steps of execution, all stuck states are values. -/
def safeN (n : Nat) : Pgm × State → Prop :=
  satN (I := I) _ _ _ n (is_value? Pgm State Val)

-- theorem safeN.mono (c : Pgm × State) (Hn : n ≤ n') (Hs : safeN _ _ n' c) : safeN _ _ n c := by
--   revert n
--   induction n'
--   · intro n Hn
--     -- Where are the Nat lemmas in core?
--     sorry
--   sorry

/-- For all terminating executions, all stuck states are values. -/
def safe (c : Pgm × State) : Prop := ∀ n, safeN (I := I) _ _ _ n c

end SmallStep
-/

/-
/-- Lift a relation on final values to a relation on program terms, which is trivially true for all non-value terms. -/
def lift_rel (R : Val × State → Val × State → Prop) (p1 p2 : Pgm × State) : Prop :=
  match SmallStep.to_value p1, SmallStep.to_value p2 with
  | some v1, some v2 => R ⟨v1, p1.2⟩ ⟨v2, p2.2⟩
  | _, _ => True


-- The product doesn't introduce "more nondeterminism" in for stuck executions.
-- If we prove that a relational property holds for all at most (n+n)-step traces that end in stuck states,
-- Then we know that for all traces of both left and right programs that take at most n steps that end in
-- stuck states, their stuck states satisfy the relation R.
-- The other direction does not hold, because the (n+n) steps don't have to by evenly divided between left
-- steps and right steps.

end Product
-/
