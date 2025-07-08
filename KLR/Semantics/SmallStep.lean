/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Semantics.Lib

/- # Mechanization of a generic nondeterministic small-Step semantics -/

/-- A small Step semantics.
Each configuration `Prog × State` nondeterministically Steps to anything in the `Step` relation.
We distinguish between error States and terminated States using the `toVal` partial function.
markusde: Having toVal be a partial function out of Prog × State rather than a total function out of
{ x : Prog × State | stuck x } is more robust against changes to the semantics.
-/
structure SmallStep : Type _ where
  /-- The type of Program terms. -/
  Prog : Type _
  /-- The type of States. -/
  State : Type _
  /-- The type of Values. -/
  Val : Type _
  /-- A nondeterministic Stepping relation. -/
  Step : Prog × State → Prog × State → Prop
  /-- Check if a Program is done, and terminate if so. -/
  toVal : Prog → Option Val
  /-- Values must not be able to execute.  -/
  toVal_isSome_isStuck {p1 p2 : Prog} {s1 s2 : State} : (toVal p1).IsSomeP → Step (p1, s1) (p2, s2) → False

/-- A small Step semantics is deterministic when every configuration is either stuck,
or Steps to exactly one State. We also force that the semantics can't take stutter steps, so that
there is exactly one way that the program can progress at each point. -/
class Det (S : SmallStep) where
  step_det {c c'} : S.Step c c' → ∀ c'', S.Step c c'' → c'' = c'
  step_progress {c c'} : S.Step c c' → c ≠ c'
export Det (step_det)

namespace SmallStep

section basic
variable (S : SmallStep)

/-- A program is a value. -/
def IsValue (p : S.Prog) : Prop := S.toVal p |>.IsSomeP

/-- A configuration is stuck. -/
def IsStuck (c : S.Prog × S.State) : Prop := ∀ {c'}, S.Step c c' → False

/-- N-step stepping relation. -/
inductive StepN : Nat → S.Prog × S.State → S.Prog × S.State → Prop where
| done : c = c' → StepN 0 c c'
| step : S.Step c c' → StepN n c' c'' → StepN n.succ c c''

/-- Demonic nontermination: There is no terminating trace.
This is stronger than the usual definition of nontermination, but is easy to work with
and equivalent to in the deterministic case. -/
def Nonterminating (c : S.Prog × S.State) : Prop :=
  ∀ {n c'}, S.StepN n c c' → ¬ S.IsStuck c'

/-- Angelic termination: There exists a terminating trace. -/
def MayTerminate (c : S.Prog × S.State) : Prop :=
  ∃ n c', S.StepN n c c' ∧ S.IsStuck c'

/-- Demonic termination: there exists N such that it is not possible for any trace to take
more than N steps. -/
def Terminating (c : S.Prog × S.State) : Prop :=
  ∃ N, ∀ c' N', N < N' → ¬S.StepN N' c c'

/-- There is exactly one state that the program can terminate in. -/
def UniquelyTerminating (c : S.Prog × S.State) : Prop :=
  ∃ N c', (S.StepN N c c') ∧ (S.IsStuck c') ∧ (∀ N'  c'', S.StepN N' c c'' → S.IsStuck c'' → N = N' ∧ c' = c'')


/-- All finite traces of a configuration only ever get stuck in value states. -/
def Safe {S : SmallStep} (c : S.Prog × S.State) : Prop :=
  ∀ {n p s}, S.StepN n c (p, s) → S.IsStuck (p, s) → S.IsValue p

theorem stepN_zero_inv (H : S.StepN 0 c c') : c = c' := by
  rcases H with ⟨rfl⟩|_; rfl

theorem step_of_stepN_one (H : S.StepN 1 c c') : S.Step c c' := by
  rcases H with _|⟨H, rfl|_⟩; exact H

theorem stepN_isStuck_inv (H : S.StepN m c c') (Hs : S.IsStuck c) : m = 0 := by
  rcases H with _|H
  · rfl
  · exact False.elim (Hs H)

theorem stepN_1_iff_step : S.StepN 1 (p, s) (p', s') ↔ S.Step (p, s) (p', s') := by
  refine ⟨?_, (StepN.step · (StepN.done rfl))⟩
  rintro (_|⟨H,He|_⟩)
  exact He▸H

theorem step_not_isStuck : S.Step (p1, s1) (p1', s1') → ¬(S.IsStuck (p1, s1)) :=
  (· |> ·)

/-- For all programs, they either map teminate, or they don't. -/
theorem weak_termination_em c : S.MayTerminate c ∨ S.Nonterminating c := by
  if Hem : S.Nonterminating c then exact .inr Hem else
  refine (.inl ?_)
  simp only [Nonterminating, Prod.forall, Classical.not_forall, not_imp, Classical.not_not] at Hem
  rcases Hem with ⟨n, p, s, _, _⟩; exists n; exists (p, s)

end basic

section det


variable {S : SmallStep} [Det S]

-- TODO: Cleanup
theorem stepN_detN {n1 n2 c'} : ∀ {c}, S.IsStuck c' → S.StepN n1 c c' → S.StepN n2 c c' → n1 = n2 := by
  intros _ _ H1
  induction H1 generalizing n2
  · intro H2
    rename_i H Hs
    exact (S.stepN_isStuck_inv H2 (H ▸ Hs)).symm
  · rename_i n c'' Hs Hsn IH Ht
    intro Hsn'
    cases n2
    · exfalso
      have H'' := S.stepN_zero_inv Hsn'; subst H''
      apply Ht Hs
    rename_i n2
    congr
    apply IH Ht
    cases Hsn'
    rename_i c'' Hs' Hsn'
    have Hx := step_det Hs _ Hs'
    exact Hx ▸ Hsn'

-- TODO: Cleanup
theorem stepN_det {n1 n2 c1 c2} (Hs : S.IsStuck c1) (Hs2 : S.IsStuck c2):
    ∀ {c}, S.StepN n1 c c1 → S.StepN n2 c c2 → n1 = n2 ∧ c1 = c2 := by
  revert c2 n2
  induction n1
  · intro n2 c2 Hs2 c Hcc1 Hcc2
    have Hcc1' := S.stepN_zero_inv Hcc1 <;> subst Hcc1'
    cases n2
    · have Hcc2' := S.stepN_zero_inv Hcc2 <;> subst Hcc2'
      exact ⟨rfl, rfl⟩
    · -- c = c1 and c1 is stuck
      rename_i n; exfalso
      cases Hcc2
      rename_i _ Hstep _
      apply Hs
      apply Hstep
  · rename_i n1 IH
    intro n2 c2 Hs2 c HstepN1 HStepN2
    cases HstepN1
    rename_i c1' Hcc1' Hc'c1
    cases n2
    · exfalso
      -- c = c2
      have Hcc2' := S.stepN_zero_inv HStepN2
      clear HStepN2
      apply (Hcc2' ▸ Hs2) Hcc1'
    rename_i n2
    simp
    apply IH
    · apply Hs2
    · apply Hc'c1
    cases HStepN2
    rename_i H1 H2 H3
    rw [← step_det Hcc1' _ H2]
    trivial

/-- For determinisic programs, if it might terminate, then it is uniquely terminating -/
theorem uniquelyTerminating_of_mayTerinate c : S.MayTerminate c → S.UniquelyTerminating c := by
  rintro ⟨N, c', Hs, Ht⟩; exact ⟨N, c', Hs, Ht, fun N' c'' Hs' Ht' => stepN_det Ht Ht' Hs Hs'⟩

/-- All deterministic programs either terminate, or they don't -/
theorem uniquelyTerminating_em c : S.UniquelyTerminating c ∨ S.Nonterminating c :=
  (S.weak_termination_em c).elim (.inl ∘ uniquelyTerminating_of_mayTerinate _) .inr

end det


/-- Our definition of program equivalence.

We consider two programs equivalent when:
- For all configurations that are initially related by Φi,
- They are equiterminating,
- All stuck states are values,
- All stuck states obey the relational invariant Φf.
-/
def PRel {S : SmallStep}
    -- TODO: Needs changing.
    -- For one, we need to fix the individual programs.
    -- I'm not sure about the relation on states. Do we care at all that the states are related?
    -- We don't in approxis, the ghost state rules out the cases where we can't step (stuck, etc.)
    -- and the resulting relation does't explicitly depend on the relationship between states.
    (c1 c2 : S.Prog × S.State)
    (Φf : (S.Val × S.State) → (S.Val × S.State) → Prop) : Prop :=
  -- c1 and c2 are equiterminating
  (S.Nonterminating c1 ↔ S.Nonterminating c2) ∧
  -- and for any two finite executions,
  (∀ c1' c2' n m,
    (S.StepN n c1 c1' ∧ S.IsStuck c1' ∧ S.StepN m c2 c2' ∧ S.IsStuck c2') →
    -- They only ever get stuck in Value States (Safety) and those Values are related by Φf
    (∃ v1 v2, S.toVal c1'.1 = some v1 ∧ S.toVal c2'.1 = some v2 ∧ Φf (v1, c1'.2) (v2, c2'.2)))

/-
/-- Monotonicity of PRel with respect to the input and output relations. -/
theorem PRel.mono {S : SmallStep} {Φi Φi' : (S.Prog × S.State) → (S.Prog × S.State) → Prop}
    {Φf Φf' : S.Val × S.State → S.Val × S.State → Prop} (Hi : ∀ {c1 c2}, Φi' c1 c2 → Φi c1 c2)
    (Hf : ∀ {c1 c2}, Φf c1 c2 → Φf' c1 c2) : PRel Φi Φf → PRel Φi' Φf' := by
  intro HRel c1 c2 HΦ
  rcases (HRel (Hi HΦ)) with ⟨Hnt, Hv⟩
  refine ⟨Hnt, ?_⟩
  intro c1' c2' n m Hstuck
  rcases (Hv c1' c2' n m Hstuck) with ⟨v1, v2, H1, H2, H3⟩
  exact ⟨v1, v2, H1, H2, Hf H3⟩
-/

/-- The equality relation on configurations. -/
def Rel.equals {S : SmallStep} : (S.Prog × S.State) → (S.Prog × S.State) → Prop := (· = ·)

/-- The relation that States that the starting Programs are equal, and the statring States both
satisfy a unary property. -/
def Rel.lift2 {S : SmallStep} (p : S.Prog) (Rs : S.State → Prop) (c1 c2 : S.Prog × S.State) : Prop :=
  c1.1 = p ∧ c2.1 = p ∧ Rs c1.2 ∧ Rs c2.2

/-- The trivial relation on configurations. -/
def Rel.triv {T : Type _} (_ _ : T) : Prop := True

/-- One relation is implied by another.

markusde: use this for the static parts of verification, eg. allocation and Value of input tensors in HBM.
-/
def Rel.implies {T : Type _} (R1 R2 : T → T → Prop) : Prop := ∀ t1 t2, R1 t1 t2 → R2 t1 t2

theorem Rel.implies_triv {T : Type _} (R : T → T → Prop) : Rel.implies R Rel.triv :=
  fun _ _ _ => trivial

/-- If a Program is related to itself with
 - The "equality" starting relation
 - the trivial terminal relation,
 then for every execution of the Program with State starting in R, that execution is Safe.

This might only make sense for deterministic semantics?
-/
theorem PRel.Safety (c : S.Prog × S.State) (Hp : PRel (S := S) c c Rel.triv) : Safe c := by
  intro n cf csf HStep Hstuck
  rcases Hp with ⟨Hterm, HVal⟩
  rcases (HVal (cf, csf) (cf, csf) n n ⟨HStep, Hstuck, HStep, Hstuck⟩) with ⟨v1, _, Hv1, Hv2, _⟩
  simp_all [IsValue]
  exact Option.IsSomeP.some

/-- A relation between two Programs such that: Φi holds for everything the left Program can Step to -/
def Rel.bind_l {S : SmallStep} (Φi : (S.Prog × S.State) → (S.Prog × S.State) → Prop)
  (cl cr : S.Prog × S.State) : Prop := ∀ cl', S.Step cl cl' -> Φi cl' cr

/-- A relation between two Programs such that: Φi holds for everything the left Program can Step to -/
def Rel.bind_r {S : SmallStep} (Φi : (S.Prog × S.State) → (S.Prog × S.State) → Prop)
  (cl cr : S.Prog × S.State) : Prop := ∀ cr', S.Step cr cr' -> Φi cl cr'

/-- Lift a relation on Values to a relation on configurations, asserting that:
 - both configurations are Values,
 - Φf holds on their Values. -/
def Rel.lift_Values {S : SmallStep} (Φf : S.Val → S.Val → Prop)
    (cl cr : S.Prog × S.State) : Prop := ∃ vl vr, S.toVal cl.1 = some vl ∧ S.toVal cr.1 = some vr ∧ Φf vl vr

theorem Rel.lift_Values_mono {S : SmallStep}  {Φ1 Φ2 : S.Val → S.Val → Prop}
    (H : Rel.implies Φ1 Φ2) : Rel.implies (Rel.lift_Values Φ1) (Rel.lift_Values Φ2) := by
  intro c1 c2 Hl
  rcases Hl with ⟨v1, v2, Hv1, Hv2, Hv12⟩
  exact ⟨v1, v2, Hv1, Hv2, H _ _ Hv12⟩

def Rel.both (P : T → Prop) (t1 t2 : T) : Prop := P t1 ∧ P t2

theorem Rel.lift_Values_triv_stuck_left {S : SmallStep} (cl cr : S.Prog × S.State)
    (H : Rel.lift_Values Rel.triv cl cr) : S.IsStuck cl := by
  rcases H with ⟨v, _, Hv, _, _⟩; intro Hs; apply Hv ▸ S.toVal_isSome_isStuck; constructor

theorem Rel.lift_Values_triv_stuck_right {S : SmallStep} (cl cr : S.Prog × S.State)
    (H : Rel.lift_Values Rel.triv cl cr) : S.IsStuck cr := by
  rcases H with ⟨_, v, _, Hv, _⟩; intro Hs; apply Hv ▸ S.toVal_isSome_isStuck; constructor

theorem Rel.lift_Values_triv_stuck_both {S : SmallStep} (cl cr : S.Prog × S.State)
  (H : Rel.lift_Values Rel.triv cl cr) : Rel.both (S.IsStuck ·) cl cr :=
  ⟨Rel.lift_Values_triv_stuck_left cl cr H, Rel.lift_Values_triv_stuck_right cl cr H⟩

/-- If either Program is not stuck, the Rel.lift_Values relation cannot hold. -/
theorem rel_lift_Values_not_stuck {S : SmallStep} (cl cr : S.Prog × S.State) {Φ}
    (H : ¬S.IsStuck cl ∨ ¬S.IsStuck cr) : ¬Rel.lift_Values Φ cl cr := by
  rintro ⟨vl, vr, Hl, Hr, _⟩
  apply H.elim
  · intro H
    apply H
    intro c
    apply Hl ▸ S.toVal_isSome_isStuck
    constructor
  · intro H
    apply H
    intro c
    apply Hr ▸ S.toVal_isSome_isStuck
    constructor

/-- If either Program is Nonterminating, the Rel.lift_Values relation cannot hold.
TODO: Use rel_lift_Values_not_stuck
-/
theorem rel_lift_Values_not_Nonterminating {S : SmallStep} (cl cr : S.Prog × S.State) {Φ}
    (H : S.Nonterminating cl ∨ S.Nonterminating cr) : ¬Rel.lift_Values Φ cl cr := by
  rintro ⟨vl, vr, Hl, Hr, _⟩
  apply H.elim
  · intro H
    apply H (n := 0) (StepN.done rfl)
    intro _
    apply Hl ▸ S.toVal_isSome_isStuck
    constructor
  · intro H
    apply H (n := 0) (StepN.done rfl)
    intro _
    apply Hr ▸ S.toVal_isSome_isStuck
    constructor

-- def Rel.both_stuck {S : SmallStep} (cl cr : S.Prog × S.State) : Prop := S.stuck cl ∧ ¬S.stuck cr

-- /-- A relation between two Programs such that:
--   - Both Programs can take a Step, and Φi holds for everything that both Programs can Step to, or
--   - Both Programs are stuck, and Φf holds for their stuck Values.-/
-- def Rel.bind_lr_sync {S : SmallStep} (Φi : (S.Prog × S.State) → (S.Prog × S.State) → Prop) (Φf : S.Val → S.Val → Prop)
--   (cl cr : S.Prog × S.State) : Prop :=
--     (Rel.lift_Values Φf cl cr) ∨
--     (Rel.both (¬S.stuck ·) cl cr ∧ ∀ cl' cr', S.Step cl cl' → S.Step cr cr' → Φi cl cr)

/- A Step-indexed version of PRel.

Assuming both programs start in Φi-related states,
  they terminate in values satisfying Φf in at most n Steps,
  or take at least n Steps.
-/
def PRelN {S : SmallStep} (n : Nat) (c1 c2 : S.Prog × S.State)
  (Φf : S.Val → S.Val → Prop) : Prop :=
  match n with
  | 0 => True
  | .succ n' =>
      -- Either they are both Values, and satisfy Φf
      (Rel.lift_Values Φf c1 c2) ∨
      -- or, there exist target States c1' c2
      -- such that the left and right sides can both take >1 Steps to reach the target States
      (∃ n1 n2 : Nat, ∃ c1' c2', S.StepN n1.succ c1 c1' ∧ S.StepN n2.succ c2 c2' ∧ PRelN n' c1' c2' Φf)


-- TODO: This is monotone. Proof: Rel.lift_Values and the other case are disjoint (because
-- it can't be both a Value, therefore stuck, and also Steppable.


-- TODO: Cleanup
theorem StepN_add_iff {S : SmallStep} {n1 n2 : Nat} {c1 c2} :
    S.StepN (n1 + n2) c1 c2 ↔ ∃ c3, S.StepN n1 c1 c3 ∧ S.StepN n2 c3 c2 := by
  revert n2 c1 c2
  induction n1
  · intro n2 c1 c2
    rw [Nat.add_comm]
    constructor
    · rw [Nat.add_zero]
      intro H
      exists c1
      exact ⟨StepN.done rfl, H⟩
    · rintro ⟨c3, ⟨He⟩, _⟩
      rw [Nat.add_zero, He]
      trivial
  · rename_i n1 IH; intro n2 c1 c2
    constructor
    · rw [Nat.add_right_comm n1 1 n2]
      intro H
      rcases H
      rename_i c3 HStep Hrest
      rcases IH.mp Hrest with ⟨x, y, z⟩
      exists x
      constructor
      · apply StepN.step HStep y
      · apply z
    · rw [Nat.add_right_comm n1 1 n2]
      rintro ⟨c3, x, y⟩
      rcases x
      rename_i a b c
      apply StepN.step b
      apply IH.mpr
      exists c3

-- Note: This theorem is not true in the presence of nondeterminism because
-- Nonterminating (Ω | 0) and Step (Ω | 0) 0 but not Nonterminating 0
theorem Nonterminating_Step [Det S] {c c'} (Hn : S.Nonterminating c) (Hs : S.Step c c') :
    S.Nonterminating c' := by
  intro n c'' Hs'
  apply Hn (n := n.succ)
  rw [Nat.succ_eq_one_add]
  apply StepN_add_iff.mpr
  exists c'
  exact ⟨StepN.step Hs (StepN.done rfl), Hs'⟩





/-

/- Deterministic Programs which satisfy PRelN for all n must be equiterminating.

Note: We require that Φi behaves like a relational invariant on the State. This can encode things
like input tensor Values, which we will be a hypothesis of our adequacy Statement. -/
theorem PRelN_terminating [Det S] {Φi Φf} {cl cr} (HΦ : Φi cl cr) (Hterm : S.Nonterminating cl)
     (Hrel : ∀ n, PRelN (S := S) n Φi Φf) : S.Nonterminating cr := by
  -- Sketch: (Rel.lift_Values Φf c1 c2) will never be true, so PRelN gets unfolded at least N times.
  -- This means that cr will take at least (gas + 1) Steps, so executing to (gas) will not be stuck.
  intro gas
  revert cl cr Φi
  induction gas
  · intro Φi cl cr HΦ Hterm Hrel
    have Hrel' := Hrel 1
    simp only [PRelN] at Hrel'
    have Hrel'' := Hrel' cl cr HΦ; clear Hrel'
    intro c' HStep0 Hstuck
    rcases Hrel'' with (H|⟨n1, n2, c1', c2', H1, H2, _⟩)
    · exact rel_lift_Values_not_Nonterminating cl cr (.inl Hterm) H
    · rcases HStep0 with ⟨Heq⟩
      rcases H2
      rename_i _ HK _
      rw [←Heq] at Hstuck
      exact Hstuck HK
  · rename_i gas IH
    intro Φi cl cr HΦ Hterm Hrel
    rintro c ⟨⟩; rename_i c' Hs Hsn
    -- Use Hrel to unfold once
    have Hrel' := Hrel (gas + 1) cl cr HΦ
    rcases Hrel' with (H|⟨n1, n2, c1', c2', H1, H2, _⟩)
    · intro Hk
      apply rel_lift_Values_not_stuck _ _ _ H
      right
      exact (· Hs)
    -- By H1 and H2, both the left and right hadn sides can take at least 1 Step.
    rcases StepN_add_iff.mp (Nat.succ_eq_one_add n1 ▸ H1) with ⟨cl_next, HStep_l, Hrest_l⟩
    rcases StepN_add_iff.mp (Nat.succ_eq_one_add n2 ▸ H2) with ⟨cr_next, HStep_r, Hrest_r⟩
    -- By HInv, Φi holds of their left and right sides
    -- have Hinv : Φi cl_next cr_next := by
    --   apply HInv.1 _ _ _ _ (S.step_of_stepN_one HStep_l)
    --   apply HInv.2 _ _ _ _ (S.step_of_stepN_one HStep_r)
    --   exact HΦ
    -- By Hterm, the new left branch is still Nonterminating
    have Hnt : S.Nonterminating cl_next := Nonterminating_Step Hterm (S.step_of_stepN_one HStep_l)
    -- Reassociate Hs and Hsn to get that the new Step takes gas Steps to get to c' (det?)
    have Hrec : S.StepN gas cr_next c := by
      have HStep_r' := S.step_of_stepN_one HStep_r
      rw [← step_det HStep_r' c' Hs]
      exact Hsn
    apply IH ?G1 Hnt Hrel Hrec
    skip
    all_goals sorry


/-- Soundness of the Step-indexed relation.
If we can prove that the relation holds for all finite traces, then PRel holds between our Programs. -/
theorem PRelN_PRel [Det S] {Φi Φf} (HInv : strong_relational_invariant Φi) :
    (∀ n, PRelN (S := S) n Φi Φf) → PRel (S := S) Φi Φf := by
  intro HP c1 c2 HΦi
  rcases uniquelyTerminating_em c1 with (Hc1 | Hc1)  <;>
  rcases uniquelyTerminating_em c2 with (Hc2 | Hc2)
  · -- Both programs terminate

    sorry
  · -- Left terminates, right doesn't. Impossible.
    exfalso
    obtain Hc1' : S.Nonterminating c1 := sorry

    sorry
  · sorry
  · sorry

  /-

  rcases SmallStep.termination_em c1 with (Hc1 | Hc1) <;>
  rcases SmallStep.termination_em c2 with (Hc2 | Hc2)
  · -- Both Programs terminate.
    constructor
    · -- False equiv Valse
      sorry
    · -- Prove: That for any two possible stuck States that we eventually Step to,
      -- they are Values where Φf holds.

      -- To do this we can prove a monotonicity lemma, it holds for all
      -- (c1' c2' : S.Prog × S.State) (n m : Nat) because it holds for Hc1.c' Hc2.c' Hc1.n Hc2.n
      -- This is because on terminating traces there is exactly ony such (n, c') pair where this holds.

      -- We need to get the Φf somehow.
      -- We need a Value for
      sorry
  · exfalso
    -- TOOD: Cleanup the PRelN_terminating proof and apply it in the other direction
    sorry
  · exfalso
    have HN : (Nonterminating c2) := PRelN_terminating HΦi Hc1 HInv HP
    rcases Hc2 with ⟨n, c', H1, H2⟩
    exact HN n c' H1 H2
  · constructor
    · simp_all
    ·
      rintro c1' c2' n m ⟨H1, H2, H3, H4⟩
      exfalso
      -- Nonterminating can't Step to a stuck State
      sorry
  -/

namespace SmallStep





/- Below: Junk -/


/-
theorem StepExactN_succ_some {n : Nat} (H : StepExactN Pgm State Val n.succ (p2', s2') (p2, s2)) :
    (SmallStep.toValue (Val := Val) (p2', s2')).isNone := by
  rcases H with (_|_)
  suffices ¬(SmallStep.toValue (Val := Val) (p2', s2')).isSome by
    generalize HX : (SmallStep.toValue (Val := Val) (p2', s2')) = X
    rw [HX] at this
    cases X <;> simp_all
  intro H
  apply (SmallStep.Value_stuck H)
  rename_i c _ _; exists c

/- A Program terminates in a given configuration in at most n Steps -/
inductive StepTerm : Nat → Pgm × State → Pgm × State → Prop where
| StepTerm_term : stuck Pgm State Val c → StepTerm n c c
| StepTerm_run : SmallStep.Step Val c c' → StepTerm n c' c'' → StepTerm n.succ c c''


def is_Value? (c : Pgm × State) : Prop := ¬ (SmallStep.toValue (Val := Val) c) = .none

/-- For the first n Steps of execution, all stuck States are Values. -/
def SafeN (n : Nat) : Pgm × State → Prop :=
  satN (I := I) _ _ _ n (is_Value? Pgm State Val)

-- theorem SafeN.mono (c : Pgm × State) (Hn : n ≤ n') (Hs : SafeN _ _ n' c) : SafeN _ _ n c := by
--   revert n
--   induction n'
--   · intro n Hn
--     -- Where are the Nat lemmas in core?
--     sorry
--   sorry

/-- For all terminating executions, all stuck States are Values. -/
def Safe (c : Pgm × State) : Prop := ∀ n, SafeN (I := I) _ _ _ n c

end SmallStep
-/

/-
/-- Lift a relation on final Values to a relation on Program terms, which is trivially true for all non-Value terms. -/
def lift_rel (R : Val × State → Val × State → Prop) (p1 p2 : Pgm × State) : Prop :=
  match SmallStep.toValue p1, SmallStep.toValue p2 with
  | some v1, some v2 => R ⟨v1, p1.2⟩ ⟨v2, p2.2⟩
  | _, _ => True


-- The product doesn't introduce "more nondeterminism" in for stuck executions.
-- If we prove that a relational property holds for all at most (n+n)-Step traces that end in stuck States,
-- Then we know that for all traces of both left and right Programs that take at most n Steps that end in
-- stuck States, their stuck States satisfy the relation R.
-- The other direction does not hold, because the (n+n) Steps don't have to by evenly divided between left
-- Steps and right Steps.

end Product
-/

/-

Stuff for when I was trying an explicit product semantics:

/-- For any of the first n Steps of execution, all stuck States satisfy `Φ`. -/
inductive satisfiesN (Φ : S.Prog × S.State → Prop) : Nat → S.Prog × S.State → Prop where
| stuck : S.stuck c → Φ c → satisfiesN Φ n c
| Step  : S.Step c c' → satisfiesN Φ n c' → satisfiesN Φ n.succ c

theorem satisfiesN_StepN (H : S.satisfiesN Φ n c) : ∀ m, m ≤ n → S.stuck c' → S.StepN m c c' → Φ c' := by
  revert c
  induction n
  · intro c H m Hm Hs Hs'
    rw [Nat.le_zero_eq] at Hm
    rcases H with ⟨_, H⟩
    exact (StepN_zero_inv S (Hm▸Hs'))▸H
  rename_i n IH
  rintro c H m Hm Hstuck HStep
  cases H
  · rename_i Hs' HΦ
    have Hz := stepN_isStuck_iff S HStep Hs'
    have Hc := StepN_zero_inv S (Hz ▸ HStep)
    exact Hc ▸ HΦ
  rename_i _ Hsat HStep'
  rcases m with (_|m)
  · exact Hstuck _ (StepN_zero_inv S HStep ▸ HStep') |>.elim
  -- have Hm' := Nat.add_le_add_iff_right ▸ Hm
  cases HStep
  -- apply IH Hsat _ (Nat.le_of_lt_succ Hm) Hstuck
  sorry
-/

/-

Product semantics stuff


@[simp] abbrev prod.Prog (S : SmallStep) := S.Prog × S.Prog
@[simp] abbrev prod.State (S : SmallStep) := S.State × S.State
@[simp] abbrev prod.Val (S : SmallStep) := S.Val × S.Val

inductive prod.Step {S : SmallStep} : (prod.Prog S) × (prod.State S) → (prod.Prog S) × (prod.State S) → Prop where
| Step_l : S.Step (p1, s1) (p1', s1') → prod.Step ((p1, p2), (s1, s2)) ((p1, p2'), (s1, s2'))
| Step_r : S.Step (p2, s2) (p2', s2') → prod.Step ((p1, p2), (s1, s2)) ((p1, p2'), (s1, s2'))

@[simp] def prod.toVal {S : SmallStep} (c : prod.Prog S × prod.State S) : Option (prod.Val S) :=
  match S.toVal ⟨c.1.1, c.2.1⟩, S.toVal ⟨c.1.2, c.2.2⟩ with
  | some v1, some v2 => some (v1, v2)
  | _, _ => none

theorem prod.Value_stuck {S : SmallStep} {c c' : prod.Prog S × prod.State S} :
    (prod.toVal c).isSome → prod.Step c c' → False := by
  rcases c with ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
  simp only [toVal]
  split
  · rename_i Hv1 Hv2
    intro _ HStep; rcases HStep with (Hs|Hs)
    · exact S.Value_stuck (Hv1▸rfl) Hs
    · exact S.Value_stuck (Hv2▸rfl) Hs
  · simp

def prod (S : SmallStep) : SmallStep where
  Prog := prod.Prog S
  State := prod.State S
  Val := prod.Val S
  Step := prod.Step
  toVal := prod.toVal
  Value_stuck := prod.Value_stuck

-/

/- I think I actually need this to be in the Step-indexed relation...

-- If we can prove a PRel starting from Rel.bind_lr_sync, then either
-- both Programs are stuck, or both Programs make Progress and satisfy PRel Φj
-- Then, we can define weakestpre by Rel.bind_lr_sync (or a stuttering variant) and
-- use this in the adequacy proof.
theorem PRel.bind_lr_sync {S : SmallStep} {c1 c2 : S.Prog × S.State}
    {Φi Φj : (S.Prog × S.State) → (S.Prog × S.State) → Prop}
    -- If c1 and c2 only ever Step from States related by Φi to States related by Φj,
    (Hij : ∀ c1' c2', S.Step c1 c1' → S.Step c2 c2' → Φi c1 c2 → Φj c1 c2)
    -- And we have established that Programs are Φj-related
    {Φf : S.Val → S.Val → Prop} :
    -- And we have established
    PRel (Rel.bind_lr_sync Φi Φf) Φf →
    Φi c1 c2 →
      ((Rel.lift_Values Φf) c1 c2) ∨
      (Rel.both (¬S.stuck ·) c1 c2 ∧ PRel (fun c1' c2' => S.Step c1 c1' → S.Step c2 c2' → Φi c1' c2') Φf)
    := sorry
-/

/-


section prod

variable {S : SmallStep}


/-- Every n-Step trace in the product semantics can be thought of as two traces in the semantics
of the components. -/
theorem prod.Step_noninterference {n : Nat} :
    S.prod.StepN n ((p, q), (s, t)) ((p', q'), (s', t')) ↔
    (∃ mₗ mᵣ : Nat, n = mₗ + mᵣ ∧ S.StepN mₗ (p, s) (p', s') ∧ S.StepN mᵣ (q, t) (q', t')) :=
  sorry

def prod.π₁ (s : S.prod.Prog × S.prod.State) : S.Prog × S.State := ⟨s.1.1, s.2.1⟩
def prod.π₂ (s : S.prod.Prog × S.prod.State) : S.Prog × S.State := ⟨s.1.2, s.2.2⟩
def prod.mk (sₗ sᵣ : S.Prog × S.State) : S.prod.Prog × S.prod.State := ⟨⟨sₗ.1, sᵣ.1⟩, ⟨sₗ.2, sᵣ.2⟩⟩

/-- Relational soundness of the product semantics: If every stuck product trace of at most (2n) Steps
satisfies Φ, then for every pair of stuck traces of at most n Steps, the relation holds on their stuck Values. -/
theorem prod.satisfies_soundness_fin {n : Nat} :
    S.prod.satisfiesN Φ (n + n) c →
    ∀ mₗ mᵣ cₗ cᵣ,
      mₗ < n → mᵣ < n →
      S.stuck cₗ → S.stuck cᵣ →
      S.StepN mₗ (prod.π₁ c) cₗ → S.StepN mₗ (prod.π₂ c) cᵣ →
      Φ (prod.mk cₗ cᵣ) :=
  sorry

end prod


/- Property of the global State which is true at every point during execution.
markusde: this is actually too strong, needs to be a part of the WP not the semantic argument.
Basically, if we want to use Φi to describe the input tensors, then we need Φi to talk about their
values, and not overwriting these values is an extrinsic property of programs in our model.
-/
def strong_relational_invariant {S : SmallStep} (Φi : S.Prog × S.State → S.Prog × S.State → Prop) : Prop :=
    (∀ cl cr cl' : S.Prog × S.State, Φi cl cr → S.Step cl cl' → Φi cl' cr) ∧
    (∀ cl cr cr' : S.Prog × S.State, Φi cl cr → S.Step cr cr' → Φi cl cr')
-/
-/
