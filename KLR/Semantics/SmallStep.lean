/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/


/- # Mechanization of a generic nondeterministic small-step semantics -/

class SmallStep (Pgm State Val : Type _) where
  step : Pgm × State → Pgm × State → Prop
  to_value : Pgm × State → Option Val
  value_stuck : (¬ to_value c = .none) → ¬ step c c'


section SmallStep

variable (Pgm State Val : Type _) [I : SmallStep Pgm State Val]

/-- A program can take exactly N steps between two states.
This implies a trace where no intermediate state is a value, and is probably not useful. -/
inductive stepExactN : Nat → Pgm × State → Pgm × State → Prop where
| step0 : stepExactN 0 c c
| stepS : SmallStep.step Val c c' → stepExactN n c' c'' → stepExactN n.succ c c''

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
  sorry
  -- satN _ _ _ n (is_value? Pgm State Val) -- what is going on here...

-- theorem safeN.mono (c : Pgm × State) (Hn : n ≤ n') (Hs : safeN _ _ n' c) : safeN _ _ n c := by
--   revert n
--   induction n'
--   · intro n Hn
--     -- Where are the Nat lemmas in core?
--     sorry
--   sorry

/-- For all terminating executions, all stuck states are values. -/
def safe (c : Pgm × State) : Prop := ∀ n, safeN _ _ n c

end SmallStep
