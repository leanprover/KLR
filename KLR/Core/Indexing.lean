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

@[simp] def List.tails {α : Type _} (L : List α) : List (List α) :=
  match L with | .nil => .nil | .cons _ L => L :: L.tails

@[simp] theorem List.tails_length {α : Type _} (L : List α) : L.tails.length = L.length := by
  induction L <;> simp; trivial

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

/-- The finite sequence of natural numbers `start + span * i` for `i < num`. -/
structure IndexSpan where
  start : Nat
  span : Int
  num : Nat
  span_nz : span ≠ 0
  get_nonneg : ∀ i : Nat, i < num → 0 ≤ start + span * i

def IndexSpan.get! (s : IndexSpan) (i : Nat) : Nat :=
  Int.toNat <| s.start + s.span * i

/-- First value outside of the span.

TODO: This is actually not true when the stride is negative and ends at zero!
not even really sure if there's a way to implement that in hardware. -/
def IndexSpan.extreme (s : IndexSpan) : Nat :=
  Int.toNat <| s.start + s.span * s.num

/-- The span [0, d) -/
def IndexSpan.full (d : Nat) : IndexSpan where
  start := 0
  span := 1
  num := d
  span_nz := Int.zero_ne_one.symm
  get_nonneg := by simp

/-- Algebraic representation of an affine function taking Nat^dim to Z -/
structure Layout (dim : Nat) where
  offset  : Nat
  strides : List Int
  nums    : List Nat
  strides_dim : strides.length = dim
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
  l.offset + (List.zipWith (fun i n => i * Int.ofNat n) l.strides c.coords).sum

/-- A list of IndexSpans with a given dimension -/
structure FreeSpans (d : Nat) where
  spans : List IndexSpan
  spans_dim : spans.length = d

/- ## Composition -/

/-- Precompose a list of FreeSpans with a layout to get another layout -/
def span_layout_comp {d} (f : FreeSpans d) (l : Layout d) : Layout d where
  offset  := -- Offset of l + Dot product of starts to each span and each layout
    l.offset + (List.zipWith (fun i n => i * Int.ofNat n) l.strides (f.spans.map IndexSpan.start)).sum.toNat
  strides := List.zipWith (· * ·) (f.spans.map IndexSpan.span) l.strides
  nums    := sorry -- Bound; some kind of minimum, not really sure yet
  strides_dim := by
    sorry
  nums_dim := by
    sorry


--   get_nonneg := sorry

def span_span_comp (s1 s2 : IndexSpan) : IndexSpan where
  start := Int.toNat <| s1.span * s2.start + s1.start
  span := s1.span * s2.span
  num := sorry -- Bound, not sure yet
  span_nz := sorry -- Not sure
  get_nonneg := sorry -- Not sure

/-
Span Semantics
-/

abbrev LayoutMap d := Layout d → Layout d

def coord_toIndexSpan (x : Nat) : IndexSpan where
  start := x
  span := 1
  num := 1
  span_nz := Int.zero_ne_one.symm
  get_nonneg := by simp

def Slice.toIndexSpan (s : Slice) (size : nat) : IndexSpan where
  start := s.l
  span := s.step
  num :=
    -- Calculate the number of steps we can take with clipping
    sorry
  span_nz := s.wf
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
  --   (l.strides.map (coeff_sum * ·))
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
      let parIndex := .slice ⟨s.start, s.extreme, s.span, s.span_nz⟩
      let freeIndices := t.shape.freeDims.map (.slice ∘ Slice.full)
      parIndex :: freeIndices
    lenWF := by simp

/-- After applying all of your FreeSpans to a Layout you end up with another layout.
Construct an AccessPattern that will extract these values from each row. -/
def CompileIndex.free_pairs (t : TensorName) (parNum : Nat) (l : Layout d) : AccessPattern where
  tensor := t
  parNum := parNum
  freePattern := List.zipWith APPair.mk l.strides l.nums
  offset := l.offset

def Layout.RowMajorForm (s : Shape) : Layout s.fdim where
  offset := 0
  strides := s.freeDims.tails.map <| Int.ofNat ∘ nat_list_prod
  nums := s.freeDims
  strides_dim := by
    sorry
  nums_dim := by
    sorry
  -- get_nonneg :=
  --   sorry

end KLR.Core
