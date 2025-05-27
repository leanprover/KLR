/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core.Basic

-- TODO: All index expressions in a composition need to be of the same dimension, for now (ie. no contraction).

def List.forall {α : Type _} (L : List α) (P : α → Prop) : Prop :=
  match L with
  | .nil => True
  | .cons l L => P l ∧ List.forall L P

/-- Get the length of the longest prefix satisfying P -/
@[simp] def List.len_max_prefix {α : Type _} (L : List α) (P : α → Bool) : Nat :=
  let rec F n L P : Nat :=
    match L with
    | .nil => n
    | .cons l L => if P l then F (n + 1) L P else n
  F 0 L P
attribute [simp] List.len_max_prefix.F

theorem List.len_max_prefix.len_mono {α : Type _} n (L : List α) (P : α → Bool) :
    n ≤ List.len_max_prefix.F n L P := by
  revert n
  induction L
  · simp
  rename_i _ _ IH; intro n
  simp; split
  · apply Nat.le_trans (n.le_add_right 1) (IH _)
  · exact Nat.le_refl n

theorem List.len_max_prefix_init_add {α : Type _} n (L : List α) (P : α → Bool) :
    List.len_max_prefix.F n L P = n + List.len_max_prefix.F 0 L P := by
  revert n
  induction L
  · intro n
    simp
  rename_i _ _ IH; intro n
  simp; split
  · conv=> rhs; rw [IH]
    rw [IH, Nat.add_assoc]
  · rfl

theorem List.len_max_prefix_eq_zero_iff {α : Type _} {L : List α} {P : α → Bool} :
    L.len_max_prefix P = 0 ↔ (L = [] ∨ ∃ l L', L = .cons l L' ∧ ¬ P l) := by
  apply Iff.intro
  · intro H
    cases L
    · left; rfl
    · right; rename_i l L; exists l; exists L
      apply And.intro rfl
      intro Hk
      simp at H; have _ := H Hk
      have _ := List.len_max_prefix.len_mono 1 L P
      omega
  · rintro (H | ⟨_, _, ⟨H, HP⟩⟩)
    · simp [H]
    · simp [H, HP]

theorem List.len_max_prefix_gt_zero_head {α : Type _} {L : List α} {P : α → Bool} :
    0 < L.len_max_prefix P → ∃ l L', L = .cons l L' ∧ P l := by
  cases L; simp
  rename_i l L
  simp; split
  · rename_i H; exact fun _ => H
  · omega

theorem List.len_max_prefix_le_length {α : Type _} {L : List α} {P : α → Bool} :
    L.len_max_prefix P ≤ L.length := by
  simp
  induction L
  · simp
  rename_i l L IH
  simp
  split
  · rw [List.len_max_prefix_init_add]; omega
  · simp

theorem List.len_max_prefix_prefix_holds  {α : Type _} {L : List α} {P : α → Bool} i :
    (h : i < L.length) → i < L.len_max_prefix P → P (L[i]) := by
  revert L
  induction i
  · intro L HL _
    cases L
    · simp at HL
    rename_i _ _ IH; simp
    rcases List.len_max_prefix_gt_zero_head IH with ⟨_, _, ⟨H, H'⟩⟩
    simp at H
    exact H.1 ▸ H'
  rename_i i IH
  simp
  intro L
  rcases L with _|⟨l, L⟩
  · simp
  simp
  intro Hlen Hi
  apply IH
  simp
  split at Hi
  · rw [List.len_max_prefix_init_add, Nat.add_comm] at Hi
    exact Nat.lt_of_add_lt_add_left Hi
  · simp at Hi

-- In Batteries!
-- @[simp] def List.tails {α : Type _} (L : List α) : List (List α) :=
--   match L with | .nil => .nil | .cons _ L => L :: L.tails
--
-- @[simp] theorem List.tails_length {α : Type _} (L : List α) : L.tails.length = L.length := by
--   induction L <;> simp; trivial


def nat_list_prod (L : List Nat) : Nat := List.foldl (· * ·) 1 L

namespace KLR.Core

/- ## Lib

TODO: Some of these defs should be moved.
-/

-- TODO: AccessBasic.get_shape should just be fixed to not return an Err, there is no reason for it
def AccessBasic.get_shape (a : AccessBasic) : Shape :=
  match H : a.shape with
  | .ok x => x
  | .error s => (AccessBasic.shape.noFail (s := s) _ H).elim

theorem AccessBasic.get_shape_length (a : AccessBasic) :
    (AccessBasic.get_shape a).freeDims.length = a.tensor.shape.freeDims.length := by
  rcases a
  rename_i _ indexes Hwf
  simp
  rcases indexes
  · exfalso; simp at Hwf
  · simp at Hwf; rw [Hwf]
    simp [AccessBasic.get_shape]
    split
    · rename_i heq; cases heq; simp
    · rename_i heq; apply (AccessBasic.shape.noFail _ heq).elim

@[simp] def Shape.fdim (s : Shape) : Nat := s.freeDims.length
@[simp] def TensorName.fdim (s : TensorName) : Nat := s.shape.fdim
@[simp] def AccessBasic.fdim (b : AccessBasic) : Nat := b.get_shape.fdim
@[simp] def AccessPattern.fdim (p : AccessPattern) : Nat := p.shape.fdim

/-- The number of free dimensions in an access.

NOTE: For now, we are only composing equal-dimensioned tensors. It should be possible to
preprocess a composition of indices into this form and it greatly simplifies the analysis. -/
def Access.fdim : Access → Nat
| .simple s => s.fdim
| .basic b => b.fdim
| .pattern p => p.fdim

/-- The slice [0, s) -/
def Slice.full (s : Nat) : Slice := ⟨0, s, 1, Int.zero_ne_one.symm⟩

/-- An Index that -/
@[simp] def AccessBasic.par_index (b : AccessBasic) : Index :=
  match H : b.indexes with
  | .nil => (Nat.add_one_ne_zero _ (List.length_nil ▸ H ▸ b.lenWF)).elim
  | .cons P _ => P

@[simp] def AccessBasic.free_indices (b : AccessBasic) : List Index :=
  match H : b.indexes with
  | .nil => (Nat.add_one_ne_zero _ (List.length_nil ▸ H ▸ b.lenWF)).elim
  | .cons _ P => P

theorem AccessBasic.free_indices_length (b : AccessBasic) :
    b.tensor.shape.freeDims.length = b.free_indices.length := by
  rcases b; rename_i indexes _
  rcases indexes <;> simp_all
  · rename_i H'; simp at H'
  · rename_i H'; simp at H'; trivial

/- ## Spans -/

/-- The finite sequence of natural numbers `start + step * i` for `i < num`. -/
structure IndexSpan where
  start : Nat
  step : Int
  num : Nat
  step_nz : step ≠ 0
  get_nonneg : ∀ i : Int, 0 ≤ i → i < num → 0 ≤ start + step * i

namespace IndexSpan

/-- Get an index from the sequence without doing any bounds checks -/
@[simp] def get! (s : IndexSpan) (i : Int) : Int :=
  s.start + s.step * i

/-- First natural number that is outside the range in the direction of s.stride.
The purpose of this function is to establish a slice bound for a given IndexSpan.

NOTE: If the last step is on zero, this just doesn't work. OTOH, if the last
step is greater than zero then anything between the last step (exclusive) and
the (last + 1) step (inclusive) is a suitable bound. Since the last step is nonnegative,
min(0, (last + 1) step) works whenever the last step is nonzero and it is impossible
if the last step is zero. -/
def extreme (s : IndexSpan) : Nat :=
  Int.toNat <| s.start + s.num * s.step

/-- As long as the last inbounds step is nonzero, the minimum of the next step and 0
(ie IndexSpan.extreme) will be outside of the range of the IndexSpan so can serve as a bound.
The num=0 and num=1 cases will be handled separately so is excluded from regular spans. -/
def is_regular (s : IndexSpan) : Bool := 1 < s.num && 0 < s.start + s.step * (s.num - 1)
def regular_wf (s : IndexSpan) : Prop := s.is_regular

/-- Convert a span to a slice. This encoding is correct when the slice is regular. -/
def regular_toSlice (s : IndexSpan) : Slice :=
  ⟨s.start, s.extreme, s.step, s.step_nz⟩

-- A common case for regular slices
theorem pos_step_regular {s : IndexSpan} (Hstep : 0 < s.step) (Hnum : 1 < s.num) :
    s.is_regular := by
  simp [IndexSpan.is_regular]
  apply And.intro Hnum
  apply Int.add_pos_of_nonneg_of_pos
  · exact Int.ofNat_zero_le s.start
  · apply Int.mul_pos Hstep
    omega

/-- In some cases where the normal formula doesn't work, we can still compile
an IndexSpan to a slice. Namely, if the IndexSpan has zero or one elements, it can
always be compiled by taking steps of size 1 in the positive direction. -/
def is_subsingleton (s : IndexSpan) : Bool := s.num <= 1
def subsingleton_wf (s : IndexSpan) : Prop := s.is_subsingleton
def subsingleton_toSlice (s : IndexSpan) : Slice :=
  ⟨s.start, s.start + s.num, 1, Int.zero_ne_one.symm⟩

/-- Compile an IndexSpan to a slice. -/
def toSlice (s : IndexSpan) : Err Slice :=
  if s.is_subsingleton then .ok s.subsingleton_toSlice else
  if s.is_regular then .ok s.regular_toSlice else
  .error "Cannot compile IndexSpan to slice"

/-- The span [0, d) -/
def full (d : Nat) : IndexSpan := ⟨0, 1, d, Int.zero_ne_one.symm, by simp; exact fun _ H _ => H⟩


/- ## Composition of two IndexSpans

An IndexSpan `(s1.comp s2) [i] = s1(s2[i])`

This composition uses clipping semantics, ie, it always returns an IndexSpan which
does "as much of (s1.comp s2) as possible". If starting out of bounds, the resulting
`num` field will be zero (not an error). -/

namespace comp

variable (s1 s2 : IndexSpan)

def start : Int :=
  s1.step * s2.start + s1.start

def step : Int :=
  s1.step * s2.step

/-- Means that `i.toNat` is an inbounds access of the IndexSpan `s`. -/
def inbounds? (s : IndexSpan) (i : Int) : Bool := 0 ≤ i && i < s.num


/-- Calculate the number of values i (starting at 0) such that `start + step  * i` is both
nonnegative and less than s2.bound. This will be the maximum (clipped) number of steps
that the composed IndexSpan can take.

TODO: There is a closed form for this, but for now we just explicitly search for the
maximum over all possible indices for s2. -/

@[simp] def num : Nat := List.len_max_prefix (List.range s2.num) (inbounds? s1 ∘ s2.get! ∘ Int.ofNat)

/-- Lemma to deal with the Int.toNat coercion in IndexSpan.clip_comp -/
theorem start_neg_implies_num_zero (H : start s1 s2 < 0) : comp.num s1 s2 = 0 := by
  apply Nat.eq_zero_of_not_pos; intro H'
  rcases (List.len_max_prefix_gt_zero_head H') with ⟨l, L, ⟨H1, H2⟩⟩
  generalize H3 : s2.num = x; cases x
  · simp [H3] at H1
  rename_i n
  rw [H3, Nat.add_comm, List.range_add] at H1
  have Hr : List.range 1 = [0] := by rfl
  simp [Hr] at H1; clear Hr
  rcases H1 with ⟨H4, H5⟩
  simp [← H4, inbounds?] at H2
  simp [start] at H
  have _ := s1.get_nonneg s2.start (Int.ofNat_zero_le _) (Int.ofNat_lt.mpr H2)
  omega

-- TODO: That naming is unfortunate
theorem num_le_ub : num s1 s2 ≤ s2.num := by
  apply Nat.le_trans List.len_max_prefix_le_length
  rw [List.length_range]
  apply Nat.le_refl

theorem get!_eq_comp : ∀ i : Int, start s1 s2 + step s1 s2 * i = s1.get! (s2.get! i) := by
  intro i
  simp [start, step, get!]
  conv=> lhs; rw [Int.add_assoc, Int.add_comm, Int.add_assoc]
  congr
  rw [Int.add_comm, Int.mul_add]
  congr 1
  apply Int.mul_assoc

end comp

/-- Defines a clipped composition operator for IndexSpans -/
def clip_comp (s1 s2 : IndexSpan) : IndexSpan where
  start := Int.toNat <| comp.start s1 s2
  step := comp.step s1 s2
  num := comp.num s1 s2
  step_nz := Int.mul_ne_zero_iff.mpr ⟨s1.step_nz, s2.step_nz⟩
  get_nonneg i Hlb Hub := by
    rcases Decidable.em (0 ≤ (comp.start s1 s2)) with (H|H)
    · rw [Int.ofNat_toNat, Int.max_eq_left H]
      rw [comp.get!_eq_comp]
      apply s1.get_nonneg _ _
      · suffices comp.inbounds? s1 (s2.get! i) by
          simp [comp.inbounds?] at this
          apply this.2
        unfold comp.num at Hub
        have Hnum := @List.len_max_prefix_prefix_holds _ (List.range s2.num)
                       (comp.inbounds? s1 ∘ s2.get! ∘ Int.ofNat)
                       i.toNat ?G1 ((Int.toNat_lt Hlb).mpr Hub)
        case G1 =>
          apply Nat.lt_of_lt_of_le ((Int.toNat_lt Hlb).mpr Hub)
          exact List.len_max_prefix_le_length
        simp at Hnum
        apply (Int.max_eq_left Hlb ▸ Hnum)
      · apply s2.get_nonneg _ Hlb
        apply Int.lt_of_lt_of_le Hub
        apply Int.ofNat_le.mpr
        exact comp.num_le_ub s1 s2
    · exfalso
      simp at H
      have Hnum := comp.start_neg_implies_num_zero (H := H)
      omega


@[simp] def clip_comp.wf (s1 s2 : IndexSpan) : Prop := 0 ≤ comp.start s1 s2

/-- As long as the composition is well-defined -/
theorem clip_comp.get!_eq (s1 s2 : IndexSpan) {i} (Hwf : clip_comp.wf s1 s2) :
    (clip_comp s1 s2).get! i = s1.get! (s2.get! i) := by
  rw [← comp.get!_eq_comp]
  simp [clip_comp]
  exact Int.max_eq_left Hwf

end IndexSpan




/- ## Layouts -/

/-- Algebraic representation of an affine function taking Nat^dim to Z -/
structure Layout (dim : Nat) where
  offset  : Nat
  steps : List Int
  nums    : List Nat
  steps_dim : steps.length = dim
  nums_dim : nums.length = dim

/-- An element of ℕ^dim -/
structure Coord (d : Nat) where
  coords : List Nat
  coords_dim : coords.length = d

/-- Every element of a Coord is inside the bounds of a particular shape -/
def Coord.inbounds (s : Shape) (c : Coord s.fdim) : Prop :=
  (List.zip c.coords s.freeDims).forall Nat.lt.uncurry

/-- Look up a memory coordinate in a layout, without doing any bounds checks -/
def Layout.get! d (l : Layout d) (c : Coord d) : Int :=
  l.offset + (List.zipWith (fun i n => i * Int.ofNat n) l.steps c.coords).sum

/-- A list of IndexSpans with a given dimension -/
structure FreeSpans (d : Nat) where
  spans : List IndexSpan
  spans_dim : spans.length = d

/- ## Composition -/

/-- Precompose a list of FreeSpans with a layout to get another layout -/
def span_layout_comp {d} (f : FreeSpans d) (l : Layout d) : Layout d where
  offset  := -- Offset of l + Dot product of starts to each span and each layout
    l.offset + (List.zipWith (fun i n => i * Int.ofNat n) l.steps (f.spans.map IndexSpan.start)).sum.toNat
  steps := List.zipWith (· * ·) (f.spans.map IndexSpan.step) l.steps
  nums  := sorry -- Bound; some kind of minimum, not really sure yet
  steps_dim := by simp [FreeSpans.spans_dim, Layout.steps_dim, Nat.min_self]
  nums_dim := by
    sorry


/-
Span Semantics
-/

abbrev LayoutMap d := Layout d → Layout d

def coord_toIndexSpan (x : Nat) : IndexSpan where
  start := x
  step := 1
  num := 1
  step_nz := Int.zero_ne_one.symm
  get_nonneg := by simp; omega

def Slice.toIndexSpan (s : Slice) (size : Nat) : IndexSpan where
  start := s.l
  step := s.step
  num :=
    -- Calculate the number of steps we can take with clipping
    sorry
  step_nz := s.wf
  get_nonneg := sorry

def Index.toIndexSpan (i : Index) (size : Nat) : IndexSpan :=
  match i with
  | .coord x => coord_toIndexSpan x
  | .slice s => s.toIndexSpan size

def simple_interp_par (t : TensorName) : IndexSpan :=
  .full t.shape.parDim

def simple_interp_free (t : TensorName) : LayoutMap t.fdim :=
  let F : FreeSpans t.fdim := ⟨t.shape.freeDims.map .full, by simp⟩
  span_layout_comp F

def basic_interp_par (b : AccessBasic) : IndexSpan :=
  b.par_index.toIndexSpan b.get_shape.parDim

def basic_interp_free (b : AccessBasic) : LayoutMap b.fdim :=
  let F : FreeSpans b.fdim := FreeSpans.mk
    (List.zipWith (·.toIndexSpan ·) b.free_indices b.get_shape.freeDims)
    (by -- Nuiscance
      -- rw [List.length_map, ← AccessBasic.free_indices_length]
      -- unfold AccessBasic.fdim
      sorry)
  span_layout_comp F

def pattern_interp_par (p : AccessPattern) : IndexSpan :=
  .full p.parNum

def pattern_interp_free (p : AccessPattern) : LayoutMap p.fdim := fun l =>
  -- TODO: Check this again
  let coeff_sum : Int := (p.freePattern.map APPair.step).sum
  sorry -- Refactor this
  -- Layout.mk
  --   (p.offset + coeff_sum * l.offset).toNat
  --   (l.steps.map (coeff_sum * ·))
  --   sorry -- List of bounds
  --   (by -- Nuiscance
  --     rw [List.length_map]
  --     sorry)
  --   (by -- Nuiscance
  --     sorry)

def Access.interp_par : Access → IndexSpan
| .simple s => simple_interp_par s
| .basic b => basic_interp_par b
| .pattern p => pattern_interp_par p

def Access.interp_free : (a : Access) → LayoutMap a.fdim
| .simple s => simple_interp_free s
| .basic b => basic_interp_free b
| .pattern p => pattern_interp_free p



/-
Execution of the compsed indexing
-/

/-- Given an IndexSpan representing the parallel indicies of a composed query, construct an
AccessBasic to extract those rows.

TODO: Is s.extreme correct here? It's weird that we're forced to put in an (exclusive?) Nat bound
in this representation, because it makes it impossible have a slice that decremenets to zero?

The construction may need to be lifted to Err & exclude the "decrement down to 0" case.
-/
def CompileIndex.par (t : TensorName) (s : IndexSpan) : AccessBasic where
    tensor := t
    indexes :=
      let parIndex := .slice ⟨s.start, s.extreme, s.step, s.step_nz⟩
      let freeIndices := t.shape.freeDims.map (.slice ∘ Slice.full)
      parIndex :: freeIndices
    lenWF := by simp

/-- After applying all of your FreeSpans to a Layout you end up with another layout.
Construct an AccessPattern that will extract these values from each row. -/
def CompileIndex.free_pairs (t : TensorName) (parNum : Nat) (l : Layout d) : AccessPattern where
  tensor := t
  parNum := parNum
  freePattern := List.zipWith APPair.mk l.steps l.nums
  offset := l.offset

def Layout.RowMajorForm (s : Shape) : Layout s.fdim where
  offset := 0
  steps := sorry -- .freeDims.tails.map <| Int.ofNat ∘ nat_list_prod -- TODO: Change tails to use batteries
  nums := s.freeDims
  steps_dim := by
    sorry
  nums_dim := by
    sorry
  -- get_nonneg :=
  --   sorry

end KLR.Core
