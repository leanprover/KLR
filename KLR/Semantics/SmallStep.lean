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

theorem IsValue_value {p : S.Prog} (H : S.IsValue p) : ∃ v, S.toVal p = some v := by
  simp_all [IsValue]
  generalize Hx : S.toVal p = x
  rw [Hx] at H
  cases x
  · cases H
  · rcases H
    rename_i v
    exists v

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

theorem stepN_1_iff_step : S.StepN 1 c1 c2 ↔ S.Step c1 c2 := by
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

theorem stepN_eq [Det S] {n c c1 c2} : S.StepN n c c1 → S.StepN n c c2 → c1 = c2 := by
  revert c
  induction n with | zero => ?_ | succ n IH => ?_
  · intro _ H1 H2; rw [← S.stepN_zero_inv H1, ← S.stepN_zero_inv H2]
  · intro c H1 H2
    rw [Nat.add_comm] at H1 H2
    obtain ⟨c1', Hc1', H1⟩ := StepN_add_iff.mp H1
    obtain ⟨c2', Hc2', H2⟩ := StepN_add_iff.mp H2
    obtain rfl : c1' = c2' := Det.step_det (S.step_of_stepN_one Hc2') _ (S.step_of_stepN_one Hc1')
    exact IH H1 H2

theorem Nonterminating_step [Det S] {c : S.Prog × S.State} (H : S.Nonterminating c) :
    ∃ c', S.Step c c' := by
  if h : S.IsStuck c
    then exact H (.done rfl) h |>.elim
    else exact Classical.not_forall_not.mp h

theorem Nonterminating_step_Nonterminating [Det S] {c : S.Prog × S.State} (H : S.Nonterminating c) (Hs : S.Step c c'):
    S.Nonterminating c' := fun HS HK' => (H (.step Hs HS) HK').elim

/-- A program steps to a value in exactly n steps -/
def StepsToValue {S : SmallStep} (n : Nat) (c : S.Prog × S.State) (v : S.Val) :=
  ∃ c', S.StepN n c c' ∧ S.toVal c'.1 = some v

/-- A program takes at least n steps -/
def StepsAtLeast {S : SmallStep} (n : Nat) (c : S.Prog × S.State) :=
  ∃ c', S.StepN n c c'

theorem StepsAtLeast_zero {S : SmallStep} {c : S.Prog × S.State} : S.StepsAtLeast 0 c :=
  ⟨c, StepN.done rfl⟩

theorem StepsAtLeast_succ [Det S] {c c' : S.Prog × S.State} (Hs : S.Step c c') (H : S.StepsAtLeast n c') :
    S.StepsAtLeast (n + 1) c := by
  rcases H with ⟨c'', Hc''⟩
  exists c''
  rw [Nat.add_comm, StepN_add_iff]
  exact ⟨c', ⟨S.stepN_1_iff_step.mpr Hs, Hc''⟩⟩

theorem Nonterminating_StepsAtLeast [Det S] {c : S.Prog × S.State} (H : S.Nonterminating c) :
    S.StepsAtLeast n c := by
  revert c
  induction n with | zero => exact fun {c} H => StepsAtLeast_zero | succ n IH => ?_
  intro c H
  rcases (Nonterminating_step H) with ⟨c', Hstep_c'⟩
  exact StepsAtLeast_succ Hstep_c' (IH <| Nonterminating_step_Nonterminating H Hstep_c')

theorem Nonterminating_not_StepsToValue [Det S] {c : S.Prog × S.State} {n : Nat} {v : S.Val}
    (Hn : S.Nonterminating c) (H : S.StepsToValue n c v) : False := by
  obtain ⟨cf, Hk⟩ := @S.Nonterminating_StepsAtLeast (n + 1) _ _ Hn
  rw [StepN_add_iff] at Hk; rcases Hk with ⟨cf', H1, H2⟩
  obtain ⟨cf'', H3, H4⟩ := H
  obtain rfl := stepN_eq H1 H3
  apply @S.toVal_isSome_isStuck cf'.1 cf.1 cf'.2 cf.2
  · rw [H4]; exact Option.IsSomeP.some
  · exact S.stepN_1_iff_step.mp H2

theorem stepN_isStuck_stepAtLeast_le [Det S] {n1 n2 : Nat} {c c' : S.Prog × S.State}
    (Hs : S.StepN n1 c c') (Hst : S.IsStuck c') (HL : S.StepsAtLeast n2 c) : n2 ≤ n1 := by
  false_or_by_contra; rename_i HK
  have HR : n2 = n1 + ((n2 - n1 - 1) + 1) := by omega
  rw [HR] at HL
  unfold StepsAtLeast at HL
  rcases HL with  ⟨c1', Hc1'⟩
  rw [StepN_add_iff] at Hc1'
  rcases Hc1' with ⟨c3, Hc3, H4⟩
  obtain rfl : c' = c3 := stepN_eq Hs Hc3
  rw [Nat.add_comm, StepN_add_iff] at H4
  rcases H4 with ⟨_, HK, _⟩
  exact Hst (S.step_of_stepN_one HK)

theorem stepN_isStuck_stepAtLeast_false [Det S] {n1 n2 : Nat} {c c' : S.Prog × S.State}
    (Hs : S.StepN n1 c c') (Hst : S.IsStuck c') (HL : S.StepsAtLeast n2 c) : n1 < n2 → False := by
  have _ := stepN_isStuck_stepAtLeast_le Hs Hst HL; omega

/-- Program equivalence.

Two programs are equivlent when they are equiterminating,
and if they terminate, they terminate in values, that are related by Φf.
-/
def PRel {S : SmallStep} (c1 c2 : S.Prog × S.State) (Φf : S.Val → S.Val → Prop) : Prop :=
  (∃ n1 n2 v1 v2, S.StepsToValue n1 c1 v1 ∧ S.StepsToValue n2 c2 v2 ∧ Φf v1 v2) ∨
  (S.Nonterminating c1 ∧ S.Nonterminating c2)

/-- Bounded stuttering -/
def PRelN {S : SmallStep} (n K : Nat) (c1 c2 : S.Prog × S.State) (Φf : S.Val → S.Val → Prop) : Prop :=
  (∃ n1 n2 v1 v2, n1 ≤ (n * K) ∧ n2 ≤ (n * K) ∧ S.StepsToValue n1 c1 v1 ∧ S.StepsToValue n2 c2 v2 ∧ Φf v1 v2) ∨
  (S.StepsAtLeast n c1 ∧ S.StepsAtLeast n c2)

-- Note: Instead of saying it stutter steps to a value, we can just condition on if it's a value
-- already. Simplifies our lives for nontrivial programs because if it's not a value we can just add
-- another stutter step in between.

def PRelS {S : SmallStep} (n K : Nat) (c1 c2 : S.Prog × S.State) (Φf : S.Val → S.Val → Prop) : Prop :=
  match n with
  | .zero => True
  | .succ n' =>
      match S.toVal c1.1, S.toVal c2.1 with
      | some v1, some v2 => Φf v1 v2
      | _, _ => ∃ n1 n2 c1' c2',
        0 < n1 ∧ 0 < n2 ∧ n1 ≤ K ∧ n2 ≤ K ∧
        S.StepN n1 c1 c1' ∧ S.StepN n2 c2 c2' ∧ S.PRelS n' K c1' c2' Φf

/-- PRel is approximated by PRelN for any stuttering bound -/
theorem PrelNLimit [Det S] (K : Nat) {c1 c2 : S.Prog × S.State} {Φf : S.Val → S.Val → Prop} :
    (∀ n, S.PRelN n K c1 c2 Φf) → S.PRel c1 c2 Φf := by
  intro Hrel
  rcases (uniquelyTerminating_em c1) with (⟨n1, c1', HStep1, HStuck1, Hut1⟩|H1) <;>
  rcases (uniquelyTerminating_em c2) with (⟨n2, c2', HStep2, HStuck2, Hut2⟩|H2)
  · rcases (Hrel ((max n1 n2) + 1)) with (H|H)
    · left
      rcases H with ⟨n1', n2', v1', v2', _, _, _, _, _⟩
      exists n1'; exists n2'; exists v1'; exists v2'
    · exfalso
      apply S.stepN_isStuck_stepAtLeast_false HStep2 HStuck2 H.2
      omega
  · rcases Hrel (n1 + 1) with (H|H)  <;> exfalso
    · rcases H with ⟨_, _, _, _, _, _, _, HK, _⟩
      exact S.Nonterminating_not_StepsToValue H2 HK
    · exact S.stepN_isStuck_stepAtLeast_false HStep1 HStuck1 H.1 n1.lt_add_one
  · rcases Hrel (n2 + 1) with (H|H)  <;> exfalso
    ·  -- Can't be the case, because c1 steps to a value but is also nonterminating
      rcases H with ⟨_, _, _, _, _, _, HK, _⟩
      exact S.Nonterminating_not_StepsToValue H1 HK
    · apply S.stepN_isStuck_stepAtLeast_false HStep2 HStuck2 H.2
      exact n2.lt_add_one
  · exact .inr ⟨H1, H2⟩


/-
theorem PRelS_trivial_core [Det S] {c1 c2 c1' c2' : S.Prog × S.State} {Φf : S.Val → S.Val → Prop} {n : Nat} :
    S.StepN n c1 c1' → S.StepN n c2 c2' → S.PRelS n c1 c2 Φf := by
  revert c1 c2 c1' c2'
  induction n; simp [PRelS]
  rename_i n' IH
  intro c1 c2 c1' c2' H1 H2
  simp only [PRelS]
  right
  obtain ⟨c1'', H1', HR1⟩ := S.StepN_add_iff.mp (Nat.add_comm _ _ ▸ H1)
  obtain ⟨c2'', H2', HR2⟩ := S.StepN_add_iff.mp (Nat.add_comm _ _ ▸ H2)
  exists 0
  exists 0
  exists c1''
  exists c2''
  refine ⟨H1', H2', IH HR1 HR2⟩
-/

/-
theorem PRelS_trivial [Det S] {c1 c2 c1' c2' : S.Prog × S.State} {Φf : S.Val → S.Val → Prop} {n nl nr : Nat} :
    S.StepN nl c1 c1' → S.StepN nr c2 c2' → n ≤ nl → n ≤ nr → S.PRelS n c1 c2 Φf := by
  revert c1 c2 c1' c2' nl nr
  induction n; simp [PRelS]
  -- rename_i n' IH
  -- intro c1 c2 c1' c2' nl nr H1 H2 Hnl Hnr
  -- simp only [PRelS]
  sorry
  -- right
  -- rcases nl with (_|nl); omega
  -- rcases nr with (_|nr); omega
  -- obtain ⟨c1'', H1', HR1⟩ := S.StepN_add_iff.mp (Nat.add_comm _ _ ▸ H1)
  -- obtain ⟨c2'', H2', HR2⟩ := S.StepN_add_iff.mp (Nat.add_comm _ _ ▸ H2)
  -- exists 0
  -- exists 0
  -- exists c1''
  -- exists c2''
  -- refine ⟨H1', H2', ?_⟩
  -- exact IH HR1 HR2 (Nat.le_of_lt_succ Hnl) (Nat.le_of_lt_succ Hnr)
-/

/-- PRelN is equivalent to the recursive version PRelS -/
theorem PRelNS [Det S] {c1 c2 : S.Prog × S.State} {Φf : S.Val → S.Val → Prop} (n : Nat) :
    S.PRelS n K c1 c2 Φf → S.PRelN n K c1 c2 Φf := by
  revert c1 c2
  induction n with | zero => ?_ | succ n IH => ?_
  · exact fun _ => .inr ⟨StepsAtLeast_zero, StepsAtLeast_zero⟩
  intro c1 c2 HrelS
  simp only [PRelS] at HrelS
  cases H1 : S.toVal c1.fst <;> cases H2 : S.toVal c2.fst <;> simp only [H1, H2] at HrelS
  · -- Neither are values, they both take between 1 and K steps.
    rcases HrelS with ⟨n1, n2, c1', c2', Hpos1, Hpos2, Hn1K, Hn2K, Hc1c1', Hc2c2', Hrec⟩
    rcases IH Hrec with (H|H)
    · -- They step to states that terminate
      left
      rcases H with ⟨n1r, n2r, v1r, v2r, Hn1r, Hn2r, Hstep1r, Hstep2r, HΦ⟩
      exists (n1r + n1)
      exists (n2r + n2)
      exists v1r
      exists v2r
      refine ⟨?_, ?_⟩
      · rw [Nat.right_distrib, Nat.one_mul]
        exact Nat.add_le_add Hn1r Hn1K
      refine ⟨?_, ?_⟩
      · rw [Nat.right_distrib, Nat.one_mul]
        exact Nat.add_le_add Hn2r Hn2K
      refine ⟨?_, ?_⟩
      · rcases Hstep1r with ⟨cv1, Hcv1, Hcv2⟩
        refine ⟨cv1, ?_, Hcv2⟩
        rw [Nat.add_comm]; apply StepN_add_iff.mpr; exists c1'
      refine ⟨?_, ?_⟩
      · rcases Hstep2r with ⟨cv1, Hcv1, Hcv2⟩
        refine ⟨cv1, ?_, Hcv2⟩
        rw [Nat.add_comm]; apply StepN_add_iff.mpr; exists c2'
      exact HΦ
    · right
      rcases H with ⟨⟨z1,Hz1⟩,⟨z2,Hz2⟩⟩
      have HFL : S.StepN (n1 + n) c1 z1 := by apply StepN_add_iff.mpr; exists c1'
      have HFR : S.StepN (n2 + n) c2 z2 := by apply StepN_add_iff.mpr; exists c2'
      rcases n1 with (_|n1); omega
      rcases n2 with (_|n2); omega
      obtain X : n1 + 1 + n = n + 1 + n1 := by omega
      rw [X] at HFL; clear X
      obtain X : n2 + 1 + n = n + 1 + n2 := by omega
      rw [X] at HFR; clear X
      refine ⟨?_, ?_⟩
      · obtain ⟨z, _, _⟩ := StepN_add_iff.mp HFL
        exists z
      · obtain ⟨z, _, _⟩ := StepN_add_iff.mp HFR
        exists z
  · exfalso
    rcases HrelS with ⟨_, nk, _, _, _, _, _, _, _, HK, _⟩
    cases nk; omega
    obtain ⟨z, HK1, _⟩ := StepN_add_iff.mp (Nat.add_comm _ _ ▸ HK)
    apply @S.toVal_isSome_isStuck c2.1 z.1 c2.2 z.2
    · rw [H2]; exact Option.IsSomeP.some
    · exact S.stepN_1_iff_step.mp HK1
  · exfalso
    rcases HrelS with ⟨nk, _, _, _, _, _, _, _, HK, _⟩
    cases nk; omega
    obtain ⟨z, HK1, _⟩ := StepN_add_iff.mp (Nat.add_comm _ _ ▸ HK)
    apply @S.toVal_isSome_isStuck c1.1 z.1 c1.2 z.2
    · rw [H1]; exact Option.IsSomeP.some
    · exact S.stepN_1_iff_step.mp HK1
  · left
    rename_i v1 v2
    exists 0; exists 0; exists v1; exists v2
    refine ⟨Nat.zero_le _, ?_⟩
    refine ⟨Nat.zero_le _, ?_⟩
    refine ⟨⟨c1, StepN.done rfl, H1⟩, ?_⟩
    refine ⟨⟨c2, StepN.done rfl, H2⟩, ?_⟩
    exact HrelS
