/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/


/- # Mechanization of a generic nondeterministic small-step semantics -/

class SmallStep (Pgm State Val : Type _) where
  step : Pgm × State → Pgm × State → Prop
  to_value : Pgm × State → Option Val
  value_stuck : (to_value c).isSome → ¬∃ c', step c c'

section SmallStep

variable (Pgm State Val : Type _) [I : SmallStep Pgm State Val]

/-- A program can take exactly N steps between two states.
This implies a trace where no intermediate state is a value, and is probably not useful. -/
inductive stepExactN : Nat → Pgm × State → Pgm × State → Prop where
| step0 : stepExactN 0 c c
| stepS : SmallStep.step Val c c' → stepExactN n c' c'' → stepExactN n.succ c c''

theorem stepExactN_1_iff_step : stepExactN Pgm State Val 1 (p, s) (p', s') ↔ I.step (p, s) (p', s') := by
  refine ⟨?_, (stepExactN.stepS · stepExactN.step0)⟩
  rintro (_|⟨_,_|_⟩)
  trivial

theorem step_none (H : SmallStep.step Val (p2', s2') (p2, s2)) :
    (SmallStep.to_value (Pgm := Pgm) (State := State) (Val := Val) (p2', s2')).isNone := by
  suffices ¬(SmallStep.to_value (Val := Val) (p2', s2')).isSome by
    generalize HX : (SmallStep.to_value (Val := Val) (p2', s2')) = X
    rw [HX] at this
    cases X <;> simp_all
  intro H'
  apply (SmallStep.value_stuck H')
  exists (p2, s2)

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

def stuck (c : Pgm × State) : Prop := ∀ c', ¬ SmallStep.step Val c c'

/- A program terminates in a given configuration in at most n steps -/
inductive stepTerm : Nat → Pgm × State → Pgm × State → Prop where
| stepTerm_term : stuck Pgm State Val c → stepTerm n c c
| stepTerm_run : SmallStep.step Val c c' → stepTerm n c' c'' → stepTerm n.succ c c''

/-- For the first n steps of execution, all stuck states satisfy `Φ`. -/
def satN (n : Nat) (Φ : Pgm × State → Prop) (c : Pgm × State) : Prop :=
  ∀ c', stepTerm _ _ Val n c c' → Φ c'

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


section Product

/- Lift a small-step semantics to product programs -/

variable {Pgm State Val : Type _} [I : SmallStep Pgm State Val]

/-- Stepping relation for product programs. -/
inductive Product.step : (Pgm × Pgm) × State × State → (Pgm × Pgm) × State × State → Prop where
| step_l : SmallStep.step Val (p1, s1) (p1', s1') → step ((p1, p2), (s1, s2)) ((p1, p2'), (s1, s2'))
| step_r : SmallStep.step Val (p2, s2) (p2', s2') → step ((p1, p2), (s1, s2)) ((p1, p2'), (s1, s2'))

def Product.to_value : (Pgm × Pgm) × State × State → Option (Val × Val)
| ((p1, p2), (s1, s2)) =>
  match I.to_value (p1, s1), I.to_value (p2, s2) with
  | .some v1, .some v2 => .some (v1, v2)
  | _, _ => .none

instance Product.is_SmallStep : SmallStep (Pgm × Pgm) (State × State) (Val × Val) where
  step := Product.step (I := I)
  to_value := Product.to_value
  value_stuck {c} := by
    rcases c with ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
    simp only [to_value]
    split
    · rename_i v1 v2 Hv1 Hv2
      intro _
      rintro ⟨c, Hc⟩
      cases Hc
      · rename_i _ Hstep
        have Hstep' := step_none Pgm State Val Hstep
        simp [Hv1] at Hstep'
      · rename_i _ Hstep
        have Hstep' := step_none Pgm State Val Hstep
        simp [Hv2] at Hstep'
    · simp

/-- Lift a relation on final values to a relation on program terms, which is trivially true for all non-value terms. -/
def lift_rel (R : Val × State → Val × State → Prop) (p1 p2 : Pgm × State) : Prop :=
  match SmallStep.to_value p1, SmallStep.to_value p2 with
  | some v1, some v2 => R ⟨v1, p1.2⟩ ⟨v2, p2.2⟩
  | _, _ => True

end Product
