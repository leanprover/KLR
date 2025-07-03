/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

/- # Mechanization of a generic nondeterministic small-step semantics -/

/-- A small step semantics.

Each configuration `prog × state` nondeterministically steps to anything in the `step` relation.
We distinguish between error states and terminated states using the `to_val` partial function.
The `val` type should include everything we want to observe about the state of our terminated programs.

markusde: Having to_val be a partial function out of prog × state rather than a total function out of
{ x : prog × state | stuck x } is more robust against changes to the semantics.
-/
structure SmallStep : Type _ where
  prog : Type _
  state : Type _
  val : Type _
  step : prog × state → prog × state → Prop
  to_val : prog × state → Option val
  value_stuck {c c' : prog × state} : (to_val c).isSome → step c c' → False

/-- A small step semantics is deterministic when every configuration is either stuck,
or steps to exactly one state. -/
class Det (S : SmallStep) where
  step_det {c c'} : S.step c c' → ∀ c'', S.step c c'' → c'' = c'

namespace SmallStep

section basic
variable (S : SmallStep)

def stuck (c : S.prog × S.state) : Prop := ∀ c', ¬ S.step c c'

inductive stepN : Nat → S.prog × S.state → S.prog × S.state → Prop where
| done : c = c' → stepN 0 c c'
| step : S.step c c' → stepN n c' c'' → stepN n.succ c c''

theorem stepN_zero_inv (H : S.stepN 0 c c') : c = c' := by cases H; trivial

theorem stepN_one (H : S.stepN 1 c c') : S.step c c' := by
  rcases H; rename_i _ H1 H2
  exact (stepN_zero_inv _ H2).symm ▸ H1

theorem stepN_stuck_inv (H : S.stepN m c c') (Hs : S.stuck c) : m = 0 := by
  cases H
  · rfl
  · rename_i Hstep HstepN
    exact (Hs _ Hstep).elim

theorem stepN_1_iff_step : S.stepN 1 (p, s) (p', s') ↔ S.step (p, s) (p', s') := by
  refine ⟨?_, (stepN.step · (stepN.done rfl))⟩
  rintro (_|⟨H,He|_⟩)
  exact He▸H

theorem step_not_stuck (H : S.step (p1, s1) (p1', s1')) : (S.to_val (p1, s1)).isNone := by
  have H' : ¬(S.to_val (p1, s1)).isSome → (S.to_val (p1, s1)).isNone := by
    cases S.to_val (p1, s1) <;> simp
  exact H' (S.value_stuck · H)

end basic


/-- All traces of a configuration do not terminate. -/
def nonterminating {S : SmallStep} (c : S.prog × S.state) : Prop :=
  -- The program never gets stuck
  ∀ n c', S.stepN n c c' → ¬ S.stuck c'

/-- All finite traces of a configuration only ever get stuck in value states. -/
def safe {S : SmallStep} (c : S.prog × S.state) : Prop :=
  ∀ n c', S.stepN n c c' → S.stuck c' → (S.to_val c').isSome

def det_stepN_unqiue [Det S] {n} : S.stepN n c c' ∧ S.stepN n c c'' → c' = c'' := by
  revert c
  induction n
  · intro _; rintro ⟨(H|_), (H'|_)⟩; exact H.symm.trans H'
  · rename_i n IH
    rintro c ⟨(_|⟨H1, H2⟩), (_|⟨H3, H4⟩)⟩
    exact IH ⟨(Det.step_det H1 _ H3) ▸ H2, H4⟩

/-- For all programs, they either surely teminate, or they don't. -/
theorem SmallStep.termination_em {S : SmallStep} c : (∃ n, ∃ c', S.stepN n c c' ∧ S.stuck c') ∨ S.nonterminating c := by
  refine (Classical.em _).elim .inr (fun H => .inl ?_)
  simp only [nonterminating, Classical.not_forall, not_imp, Classical.not_not] at H
  rcases H with ⟨n, c', H, Hs⟩
  exists n
  exists c'

/-- A conservative definition of program equivalence, which should work as long as our semantics
is deterministic.

This is the thing we eventually want to prove about our programs.
-/
def PRel {S : SmallStep}
    (Φi : (S.prog × S.state) → (S.prog × S.state) → Prop)
    (Φf : S.val → S.val → Prop) : Prop :=
  -- For all starting configurations that are related by Φi,
  ∀ {c1 c2}, Φi c1 c2 →
  -- They are equiterminating,
  (nonterminating c1 ↔ nonterminating c2) ∧
  -- and for any two finite executions,
  (∀ c1' c2' n m,
    (S.stepN n c1 c1' ∧ S.stuck c1' ∧ S.stepN m c2 c2' ∧ S.stuck c2') →
    -- They only ever get stuck in value states (safety) and those values are related by Φf
    (∃ v1 v2, S.to_val c1' = some v1 ∧ S.to_val c2' = some v2 ∧ Φf v1 v2))

/-- Monotonicity of PRel with respect to the input and output relations. -/
theorem PRel.mono {S : SmallStep} {Φi Φi' : (S.prog × S.state) → (S.prog × S.state) → Prop}
    {Φf Φf' : S.val → S.val → Prop} (Hi : ∀ {c1 c2}, Φi' c1 c2 → Φi c1 c2)
    (Hf : ∀ {c1 c2}, Φf c1 c2 → Φf' c1 c2) : PRel Φi Φf → PRel Φi' Φf' := by
  intro HRel c1 c2 HΦ
  rcases (HRel (Hi HΦ)) with ⟨Hnt, Hv⟩
  refine ⟨Hnt, ?_⟩
  intro c1' c2' n m Hstuck
  rcases (Hv c1' c2' n m Hstuck) with ⟨v1, v2, H1, H2, H3⟩
  exact ⟨v1, v2, H1, H2, Hf H3⟩


/-- The equality relation on configurations. -/
def Rel.equals {S : SmallStep} : (S.prog × S.state) → (S.prog × S.state) → Prop := (· = ·)

/-- The relation that states that the starting programs are equal, and the statring states both
satisfy a unary property. -/
def Rel.lift2 {S : SmallStep} (p : S.prog) (Rs : S.state → Prop) (c1 c2 : S.prog × S.state) : Prop :=
  c1.1 = p ∧ c2.1 = p ∧ Rs c1.2 ∧ Rs c2.2

/-- The trivial relation on configurations. -/
def Rel.triv {T : Type _} (_ _ : T) : Prop := True

/-- One relation is implied by another.

markusde: use this for the static parts of verification, eg. allocation and value of input tensors in HBM.
-/
def Rel.implies {T : Type _} (R1 R2 : T → T → Prop) : Prop := ∀ t1 t2, R1 t1 t2 → R2 t1 t2

theorem Rel.implies_triv {T : Type _} (R : T → T → Prop) : Rel.implies R Rel.triv :=
  fun _ _ _ => trivial

/-- If a program is related to itself with
 - The "equality" starting relation
 - the trivial terminal relation,
 then for every execution of the program with state starting in R, that execution is safe.

This might only make sense for deterministic semantics?
-/
theorem PRel.safety {S : SmallStep} p (R : S.state → Prop) (Hp : PRel (Rel.lift2 p R) Rel.triv) :
    ∀ {s : S.state}, R s → safe (p, s) := by
  intro s Hr n cf Hstep Hstuck
  have HRi : Rel.lift2 p R (p, s) (p, s) := ⟨rfl, rfl, Hr, Hr⟩
  rcases (Hp HRi) with ⟨Hterm, Hval⟩
  rcases (Hval cf cf n n ⟨Hstep, Hstuck, Hstep, Hstuck⟩) with ⟨v1, _, Hv1, _, _⟩
  rw [Hv1]; rfl

/-- A relation between two programs such that: Φi holds for everything the left program can step to -/
def Rel.bind_l {S : SmallStep} (Φi : (S.prog × S.state) → (S.prog × S.state) → Prop)
  (cl cr : S.prog × S.state) : Prop := ∀ cl', S.step cl cl' -> Φi cl' cr

/-- A relation between two programs such that: Φi holds for everything the left program can step to -/
def Rel.bind_r {S : SmallStep} (Φi : (S.prog × S.state) → (S.prog × S.state) → Prop)
  (cl cr : S.prog × S.state) : Prop := ∀ cr', S.step cr cr' -> Φi cl cr'

/-- Lift a relation on values to a relation on configurations, asserting that:
 - both configurations are values,
 - Φf holds on their values. -/
def Rel.lift_values {S : SmallStep} (Φf : S.val → S.val → Prop)
    (cl cr : S.prog × S.state) : Prop := ∃ vl vr, S.to_val cl = some vl ∧ S.to_val cr = some vr ∧ Φf vl vr

theorem Rel.lift_values_mono {S : SmallStep}  {Φ1 Φ2 : S.val → S.val → Prop}
    (H : Rel.implies Φ1 Φ2) : Rel.implies (Rel.lift_values Φ1) (Rel.lift_values Φ2) := by
  intro c1 c2 Hl
  rcases Hl with ⟨v1, v2, Hv1, Hv2, Hv12⟩
  exact ⟨v1, v2, Hv1, Hv2, H _ _ Hv12⟩

def Rel.both (P : T → Prop) (t1 t2 : T) : Prop := P t1 ∧ P t2

theorem Rel.lift_values_triv_stuck_left {S : SmallStep} (cl cr : S.prog × S.state)
    (H : Rel.lift_values Rel.triv cl cr) : S.stuck cl := by
  rcases H with ⟨v, _, Hv, _, _⟩; intro Hs; apply Hv ▸ S.value_stuck; rfl

theorem Rel.lift_values_triv_stuck_right {S : SmallStep} (cl cr : S.prog × S.state)
    (H : Rel.lift_values Rel.triv cl cr) : S.stuck cr := by
  rcases H with ⟨_, v, _, Hv, _⟩; intro Hs; apply Hv ▸ S.value_stuck; rfl

theorem Rel.lift_values_triv_stuck_both {S : SmallStep} (cl cr : S.prog × S.state)
  (H : Rel.lift_values Rel.triv cl cr) : Rel.both (S.stuck ·) cl cr :=
  ⟨Rel.lift_values_triv_stuck_left cl cr H, Rel.lift_values_triv_stuck_right cl cr H⟩

/-- If either program is not stuck, the Rel.lift_values relation cannot hold. -/
theorem rel_lift_values_not_stuck {S : SmallStep} (cl cr : S.prog × S.state) {Φ}
    (H : ¬S.stuck cl ∨ ¬S.stuck cr) : ¬Rel.lift_values Φ cl cr := by
  rintro ⟨vl, vr, Hl, Hr, _⟩
  apply H.elim
  · intro H
    apply H
    intro c
    apply Hl ▸ S.value_stuck (c := cl)
    rfl
  · intro H
    apply H
    intro c
    apply Hr ▸ S.value_stuck (c := cr)
    rfl

/-- If either program is nonterminating, the Rel.lift_values relation cannot hold.
TODO: Use rel_lift_values_not_stuck
-/
theorem rel_lift_values_not_nonterminating {S : SmallStep} (cl cr : S.prog × S.state) {Φ}
    (H : nonterminating cl ∨ nonterminating cr) : ¬Rel.lift_values Φ cl cr := by
  rintro ⟨vl, vr, Hl, Hr, _⟩
  apply H.elim
  · intro H
    apply (H 0 cl (stepN.done rfl))
    intro _
    apply Hl ▸ S.value_stuck
    rfl
  · intro H
    apply (H 0 cr (stepN.done rfl))
    intro _
    apply Hr ▸ S.value_stuck
    rfl

-- def Rel.both_stuck {S : SmallStep} (cl cr : S.prog × S.state) : Prop := S.stuck cl ∧ ¬S.stuck cr

-- /-- A relation between two programs such that:
--   - Both programs can take a step, and Φi holds for everything that both programs can step to, or
--   - Both programs are stuck, and Φf holds for their stuck values.-/
-- def Rel.bind_lr_sync {S : SmallStep} (Φi : (S.prog × S.state) → (S.prog × S.state) → Prop) (Φf : S.val → S.val → Prop)
--   (cl cr : S.prog × S.state) : Prop :=
--     (Rel.lift_values Φf cl cr) ∨
--     (Rel.both (¬S.stuck ·) cl cr ∧ ∀ cl' cr', S.step cl cl' → S.step cr cr' → Φi cl cr)

/- A step-indexed version of PRel.

Both programs need to either terminate in values satisfying Φf in at most n steps,
or take at least n steps.
-/
def PRelN {S : SmallStep} (n : Nat) (Φi : (S.prog × S.state) → (S.prog × S.state) → Prop) (Φf : S.val → S.val → Prop) : Prop :=
  match n with
  | 0 => True
  | .succ n' =>
      -- For any two initial states that are related by Φi
      ∀ c1 c2, Φi c1 c2 →
      -- Either they are both values, and satisfy Φf
      (Rel.lift_values Φf c1 c2) ∨
      -- or, there exist target states c1' c2
      -- such that the left and right sides can both take >1 steps to reach the target states
      (∃ n1 n2 : Nat, ∃ c1' c2',
          S.stepN n1.succ c1 c1' ∧
          S.stepN n2.succ c2 c2' ∧
          PRelN n' (fun ρ1 ρ2 => ρ1 = c1' ∧ ρ2 = c2) Φf)

-- TODO: This is monotone. Proof: Rel.lift_values and the other case are disjoint (because
-- it can't be both a value, therefore stuck, and also steppable.

/-- Property of the global state which is true at every point during execution. -/
def strong_relational_invariant {S : SmallStep} (Φi : S.prog × S.state → S.prog × S.state → Prop) : Prop :=
    (∀ cl cr cl' : S.prog × S.state, Φi cl cr → S.step cl cl' → Φi cl' cr) ∧
    (∀ cl cr cr' : S.prog × S.state, Φi cl cr → S.step cr cr' → Φi cl cr')

-- TODO: Cleanup
theorem stepN_add_iff {S : SmallStep} {n1 n2 : Nat} {c1 c2} :
    S.stepN (n1 + n2) c1 c2 ↔ ∃ c3, S.stepN n1 c1 c3 ∧ S.stepN n2 c3 c2 := by
  revert n2 c1 c2
  induction n1
  · intro n2 c1 c2
    rw [Nat.add_comm]
    constructor
    · rw [Nat.add_zero]
      intro H
      exists c1
      exact ⟨stepN.done rfl, H⟩
    · rintro ⟨c3, ⟨He⟩, _⟩
      rw [Nat.add_zero, He]
      trivial
  · rename_i n1 IH; intro n2 c1 c2
    constructor
    · rw [Nat.add_right_comm n1 1 n2]
      intro H
      rcases H
      rename_i c3 Hstep Hrest
      rcases IH.mp Hrest with ⟨x, y, z⟩
      exists x
      constructor
      · apply stepN.step Hstep y
      · apply z
    · rw [Nat.add_right_comm n1 1 n2]
      rintro ⟨c3, x, y⟩
      rcases x
      rename_i a b c
      apply stepN.step b
      apply IH.mpr
      exists c3

-- Note: This theorem is not true in the presence of nondeterminism because
-- nonterminating (Ω | 0) and step (Ω | 0) 0 but not nonterminating 0
theorem nonterminating_step [Det S] {c c'} (Hn : nonterminating c) (Hs : S.step c c') :
    nonterminating c' := by
  intro n c'' Hs'
  apply Hn n.succ
  rw [Nat.succ_eq_one_add]
  apply stepN_add_iff.mpr
  exists c'
  exact ⟨stepN.step Hs (stepN.done rfl), Hs'⟩


/- Deterministic programs which satisfy PRelN for all n must be equiterminating.

Note: We require that Φi behaves like a relational invariant on the state. This can encode things
like input tensor values, which we will be a hypothesis of our adequacy statement. -/
theorem PRelN_terminating [Det S] {Φi Φf} {cl cr} (HΦ : Φi cl cr) (Hterm : nonterminating cl)
    (HInv : strong_relational_invariant Φi) (Hrel : ∀ n, PRelN (S := S) n Φi Φf) : nonterminating cr := by
  -- Sketch: (Rel.lift_values Φf c1 c2) will never be true, so PRelN gets unfolded at least N times.
  -- This means that cr will take at least (gas + 1) steps, so executing to (gas) will not be stuck.
  intro gas
  revert cl cr
  induction gas
  · intro cl cr HΦ Hterm
    have Hrel' := Hrel 1
    simp only [PRelN] at Hrel'
    have Hrel'' := Hrel' cl cr HΦ; clear Hrel'
    intro c' Hstep0 Hstuck
    rcases Hrel'' with (H|⟨n1, n2, c1', c2', H1, H2, _⟩)
    · exact rel_lift_values_not_nonterminating cl cr (.inl Hterm) H
    · rcases Hstep0 with ⟨Heq⟩
      rcases H2
      rename_i _ HK _
      rw [←Heq] at Hstuck
      exact Hstuck _ HK
  · rename_i gas IH
    intro cl cr HΦ Hterm
    rintro c ⟨⟩; rename_i c' Hs Hsn
    -- Use Hrel to unfold once
    have Hrel' := Hrel (gas + 1) cl cr HΦ <;> clear Hrel
    rcases Hrel' with (H|⟨n1, n2, c1', c2', H1, H2, _⟩)
    · intro Hk
      apply rel_lift_values_not_stuck _ _ _ H
      right
      exact fun a => a c' Hs
    -- By H1 and H2, both the left and right hadn sides can take at least 1 step.
    rcases stepN_add_iff.mp (Nat.succ_eq_one_add n1 ▸ H1) with ⟨cl_next, Hstep_l, Hrest_l⟩
    rcases stepN_add_iff.mp (Nat.succ_eq_one_add n2 ▸ H2) with ⟨cr_next, Hstep_r, Hrest_r⟩
    -- By HInv, Φi holds of their left and right sides
    have Hinv : Φi cl_next cr_next := by
      apply HInv.1 _ _ _ _ (S.stepN_one Hstep_l)
      apply HInv.2 _ _ _ _ (S.stepN_one Hstep_r)
      exact HΦ
    -- By Hterm, the new left branch is still nonterminating
    have Hnt : nonterminating cl_next := nonterminating_step Hterm (S.stepN_one Hstep_l)
    -- Reassociate Hs and Hsn to get that the new step takes gas steps to get to c' (det?)
    have Hrec : S.stepN gas cr_next c := by
      have Hstep_r' := S.stepN_one Hstep_r
      rw [← Det.step_det Hstep_r' c' Hs]
      exact Hsn
    exact IH Hinv Hnt _ Hrec



/-- Soundness of the step-indexed relation.
If we can prove that the relation holds for all finite traces, then PRel holds between our programs. -/
theorem PRelN_PRel [Det S] {Φi Φf} (HInv : strong_relational_invariant Φi) :
    (∀ n, PRelN (S := S) n Φi Φf) → PRel (S := S) Φi Φf := by
  intro HP c1 c2 HΦi
  rcases SmallStep.termination_em c1 with (Hc1 | Hc1) <;>
  rcases SmallStep.termination_em c2 with (Hc2 | Hc2)
  · -- Both programs terminate.
    constructor
    · -- False equiv valse
      sorry
    · -- Prove: That for any two possible stuck states that we eventually step to,
      -- they are values where Φf holds.

      -- To do this we can prove a monotonicity lemma, it holds for all
      -- (c1' c2' : S.prog × S.state) (n m : Nat) because it holds for Hc1.c' Hc2.c' Hc1.n Hc2.n
      -- This is because on terminating traces there is exactly ony such (n, c') pair where this holds.

      -- We need to get the Φf somehow.
      -- We need a value for
      sorry
  · exfalso
    -- TOOD: Cleanup the PRelN_terminating proof and apply it in the other direction
    sorry
  · exfalso
    have HN : (nonterminating c2) := PRelN_terminating HΦi Hc1 HInv HP
    rcases Hc2 with ⟨n, c', H1, H2⟩
    exact HN n c' H1 H2
  · constructor
    · simp_all
    ·
      rintro c1' c2' n m ⟨H1, H2, H3, H4⟩
      exfalso
      -- Nonterminating can't step to a stuck state
      sorry

namespace SmallStep





/- Below: Junk -/


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

/-

Stuff for when I was trying an explicit product semantics:

/-- For any of the first n steps of execution, all stuck states satisfy `Φ`. -/
inductive satisfiesN (Φ : S.prog × S.state → Prop) : Nat → S.prog × S.state → Prop where
| stuck : S.stuck c → Φ c → satisfiesN Φ n c
| step  : S.step c c' → satisfiesN Φ n c' → satisfiesN Φ n.succ c

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

/-

Product semantics stuff


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

-/

/- I think I actually need this to be in the step-indexed relation...

-- If we can prove a PRel starting from Rel.bind_lr_sync, then either
-- both programs are stuck, or both programs make progress and satisfy PRel Φj
-- Then, we can define weakestpre by Rel.bind_lr_sync (or a stuttering variant) and
-- use this in the adequacy proof.
theorem PRel.bind_lr_sync {S : SmallStep} {c1 c2 : S.prog × S.state}
    {Φi Φj : (S.prog × S.state) → (S.prog × S.state) → Prop}
    -- If c1 and c2 only ever step from states related by Φi to states related by Φj,
    (Hij : ∀ c1' c2', S.step c1 c1' → S.step c2 c2' → Φi c1 c2 → Φj c1 c2)
    -- And we have established that programs are Φj-related
    {Φf : S.val → S.val → Prop} :
    -- And we have established
    PRel (Rel.bind_lr_sync Φi Φf) Φf →
    Φi c1 c2 →
      ((Rel.lift_values Φf) c1 c2) ∨
      (Rel.both (¬S.stuck ·) c1 c2 ∧ PRel (fun c1' c2' => S.step c1 c1' → S.step c2 c2' → Φi c1' c2') Φf)
    := sorry
-/

/-


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
