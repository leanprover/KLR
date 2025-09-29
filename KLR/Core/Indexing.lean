/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import KLR.Core.Basic

/- # Semantics of Indexing Operations

This file defines the interpretation of `Access` statements, and a technique for
composing sequences of `Access` statements as well.

## Semantics

Every access statement has
- A dimension
- A shape

When applied to a tensor of the same dimension, it represents a subtensor having the same
dimension but with a different shape. In this file, shapes are free to have size zero
along any access, and we do not contract dimensions with size 1 (as Numpy does in some cases
but not others).

There are two main variants of the semantics
- A "clipping" semantics, where out-of-bounds accesses are ignored,
- A "total" semantics, where out-of-bounds accesses are UB.
Numpy uses a "clipping" semantics for some tensor accesses (like slices) and a "total" semantics
for others (like slices of size 1). This file does not match Numpy exactly.

Our model of an access uses these types:
- An `IndexSpan`, which denotes a finite affine sequence of nonnegative integers
- A `FreeSpans d`, which is a length-indexed list of `IndexSpan`s
- A `Layout d`, denoting an affine function from `Int^d to Int`
- A `LayoutMap d`, ie. a function `Layout d → Layout d`.

The semantics for each access term is given in two parts
- An `IndexSpan` describing the indices of the parallel dimension of the view as a function of
  the parallel dimension of the initial tensor.
  + See `Access.interpPar`
- A `LayoutMap` describing where each free index of the view lives in memory, given an affine
  layout of the initial tensor in memory.
  + See `Access.interpFree`

All of `IndexSpan`s, `FreeSpan`s, and `Layout`s have a `get!` function plus some notion of
an input being "inbounds". The semantics of a list of Access operations is the composition of
these `get!` functions is the composition of these `get!` functions if the output of each
function is inbounds, or `UB` if out-of-bounds.


## Composition

The key insights are the following:
- `IndexSpan`s and `Layout`s compose in the same way affine functions do.
  + See `clipComp` and `lcomp.comp` respectively
- An access along the par dimension[^1] described by an `IndexSpan` can be realized by an `AccessBasic`
  + See `CompileIndex.par`
- An access along the free dimension described by a `Layout` can be realized by an `AccessPattern`
  + See `CompileIndex.freePairs`

Hence, if we know the memory layout is a multi-affine function (for example, `Layout.rowMajorForm`),
then we can compose the par and free dimensions for each access separately, leaving at most one `AccessBasic`
and at most one `AccessPattern`. These could be further optimized out if either access is trivial.


## Static Semantics

For the simple and basic accesses, we use clipping semantics. That is, we define the bound on the input
to be the greatest integer such that each access is inboubds. For example, the clipping semantics for a
an access `A[2:25]` for a tensor `A` with shape `(10,)` would establish the input bounds to be `(8,)`.

There is no analogue for access patterns, the clipping semantics for access patterns is ambiguous.
Suppose for example we have a 2D tensor of shape (4, 4) and we're accessing it via the
pattern [0, (1, 20), (1,20)]. There are a total of 16 locations allocated in memory, we could choose
to clip this resulting tensor to have shape (A, B) for any values of A, B with product at most 16 and
it would make sense. Hence, we use a total semantics for access patterns.

Thus, the semantics of a sequence of accesses depend in general on the shape of the input tensor.

Furthermore, this file currently only supports compositions of equal-dimensioned tensors.
In Numpy, some dimensions with size 1 are contracted, so for example an access `A[:,2,:][3:5, 4:2:-1]`
would be legal because the `[:,2,:]` access results in a 2-dimensional view of the 3-dimensional tensor `A`.
Numpy doesn't always contract such dimensions, for example it does not contract `A[:,2:3,:]` even though
this view has the same elements as `[:,2,:]`. If we seek to support the same thing, we could make a pass
through a list of indices to undo the contraction of all `.coord` slices.

## Footnotes

[^1]: An access along the par dimension with negative stride whose last element is zero cannot
be realized.
-/

section Lib
-- TODO: Move this section somewhere else
def List.Forall {α : Type _} (L : List α) (P : α → Prop) :=
  match L with | .nil => True | .cons l L => P l ∧ List.Forall L P

/-- Get the length of the longest prefix satisfying P -/
@[simp] def List.lenMaxPrefix {α : Type _} (L : List α) (P : α → Bool) : Nat :=
  let rec F n L P : Nat :=
    match L with
    | .nil => n
    | .cons l L => if P l then F (n + 1) L P else n
  F 0 L P
attribute [simp] List.lenMaxPrefix.F

theorem List.lenMaxPrefix.len_mono {α : Type _} (L : List α) (P : α → Bool) :
    ∀ n, n ≤ List.lenMaxPrefix.F n L P := by
  induction L with | nil => simp | cons _ _ IH => ?_
  simp only [F]; split
  · exact (Nat.le_of_succ_le <| IH ·.succ)
  · exact Nat.le_refl

theorem List.lenMaxPrefix_init_add {α : Type _} (L : List α) (P : α → Bool) :
    ∀ n, List.lenMaxPrefix.F n L P = n + List.lenMaxPrefix.F 0 L P := by
  induction L with | nil => simp | cons _ _ IH => ?_
  simp only [lenMaxPrefix.F]; split
  · intro n
    conv=> rhs; rw [IH]
    rw [IH, Nat.add_assoc]
  · exact fun _ => rfl

theorem List.lenMaxPrefix_eq_zero_iff {α : Type _} {L : List α} {P : α → Bool} :
    L.lenMaxPrefix P = 0 ↔ (L = [] ∨ ∃ l L', L = .cons l L' ∧ ¬ P l) := by
  apply Iff.intro
  · intro H
    rcases L with (_|⟨l, L⟩)
    · exact .inl rfl
    · refine .inr ⟨l, L, ⟨rfl, fun Hk => ?_⟩⟩
      simp at H
      have _ := H Hk
      have _ := List.lenMaxPrefix.len_mono  L P 1
      omega
  · rintro (H | ⟨_, _, ⟨H, HP⟩⟩) <;> simp [H]
    exact (HP · |>.elim)

theorem List.lenMaxPrefix_gt_zero_head {α : Type _} {L : List α} {P : α → Bool} :
    0 < L.lenMaxPrefix P → ∃ l L', L = .cons l L' ∧ P l := by
  rcases L with (_|⟨l, L⟩) <;> simp
  split
  · rename_i H; exact fun _ => H
  · omega

theorem List.lenMaxPrefix_le_length {α : Type _} {L : List α} {P : α → Bool} :
    L.lenMaxPrefix P ≤ L.length := by
  simp only [lenMaxPrefix]
  induction L with | nil => simp | cons l L IH => ?_
  simp only [lenMaxPrefix.F, length_cons]
  split
  · rw [List.lenMaxPrefix_init_add]
    omega
  · simp

theorem List.lenMaxPrefix_prefix_holds  {α : Type _} {L : List α} {P : α → Bool} i :
    (h : i < L.length) → i < L.lenMaxPrefix P → P (L[i]) := by
  revert L
  induction i
  · intro L HL _; rename_i IH
    rcases L; simp at HL
    rcases List.lenMaxPrefix_gt_zero_head IH with ⟨_, _, ⟨H, H'⟩⟩
    exact (cons.injEq _ _ _ _ ▸ H).1 ▸ H'
  rename_i i IH
  intro L
  rcases L with _|⟨l, L⟩ <;> simp
  intro Hlen Hi
  split at Hi
  · rw [List.lenMaxPrefix_init_add, Nat.add_comm] at Hi
    exact IH _ (Nat.lt_of_add_lt_add_left Hi)
  · simp at Hi

@[simp] def List.tails' {α : Type _} (L : List α) : List (List α) :=
  match L with | .nil => .nil | .cons _ L => L :: L.tails'

@[simp] theorem List.tails'_length {α : Type _} (L : List α) : L.tails'.length = L.length := by
  induction L <;> simp; trivial

def natListProd (L : List Nat) : Nat := List.foldl (· * ·) 1 L

def List.dot [Mul α] [Add α] [Zero α] (L1 L2 : List α) : α :=
  (List.zipWith (· * ·) L1 L2).sum

theorem List.dot_comm (L1 L2 : List Int) : L1.dot L2 = L2.dot L1 :=
  congrArg _ <| zipWith_comm_of_comm Int.mul_comm

end Lib

namespace KLR.Core

-- TODO: Move some of these definitions to Basic

-- TODO: AccessBasic.getShape should just be fixed to not return an Err, there is no reason for it
def AccessBasic.getShape (a : AccessBasic) : Shape :=
  match H : a.shape with
  | .ok x => x
  | .error s => (shape.noFail (s := s) _ H).elim

theorem AccessBasic.getShape_length (a : AccessBasic) :
    (AccessBasic.getShape a).freeDims.length = a.tensor.shape.freeDims.length := by
  rcases a
  rename_i _ indexes Hwf
  rcases indexes <;> simp at Hwf
  rw [Hwf]
  simp only [AccessBasic.getShape]
  split
  · rename_i heq; cases heq; simp
  · rename_i heq; apply (AccessBasic.shape.noFail _ heq).elim

@[simp] def Shape.freeDim (s : Shape) : Nat := s.freeDims.length
@[simp] def TensorName.freeDim (s : TensorName) : Nat := s.shape.freeDim
@[simp] def AccessBasic.freeDim (b : AccessBasic) : Nat := b.getShape.freeDim
@[simp] def AccessPattern.freeDim (p : AccessPattern) : Nat := p.shape.freeDim

/-- The number of free dimensions in an access. -/
def Access.freeDim : Access → Nat
| .simple s => s.freeDim
| .basic b => b.freeDim
| .pattern p => p.freeDim
| .birPattern _ => 0  -- TODO: should not occur

/-- The slice [0, s) -/
def Slice.full (s : Nat) : Slice := ⟨0, s, 1, Int.zero_ne_one.symm⟩

/-- Obtain the first element of the .indexes field -/
@[simp] def AccessBasic.parIndex (b : AccessBasic) : Index :=
  match H : b.indexes with
  | .nil => (Nat.add_one_ne_zero _ (List.length_nil ▸ H ▸ b.lenWF)).elim
  | .cons P _ => P

/-- Obtain all but the first element of the .indexes field -/
@[simp] def AccessBasic.freeIndices (b : AccessBasic) : List Index :=
  match H : b.indexes with
  | .nil => (Nat.add_one_ne_zero _ (List.length_nil ▸ H ▸ b.lenWF)).elim
  | .cons _ P => P

theorem AccessBasic.freeIndices_length (b : AccessBasic) :
    b.tensor.shape.freeDims.length = b.freeIndices.length := by
  rcases b with ⟨_, ⟨⟩, _⟩ <;> rename_i H' <;> simp at H'; trivial

/- ## Spans -/

/-- The finite sequence of natural numbers `start + step * i` for `i < num`. -/
structure IndexSpan where
  start : Nat
  step : Int
  num : Nat
  step_nz : step ≠ 0
  get_nonneg : ∀ i : Int, 0 ≤ i → i < num → 0 ≤ start + step * i
  deriving Repr

namespace IndexSpan

instance : Inhabited IndexSpan where
  default := {
    start := 0
    step := 1
    num := 0
    step_nz := Int.one_ne_zero
    get_nonneg := by intros; simp; trivial
  }

/-- Get an index from the sequence without doing any bounds checks -/
@[simp] def get! (s : IndexSpan) (i : Int) : Int := s.start + s.step * i

/-- First natural number that is outside the range in the direction of s.stride.
The purpose of this function is to establish a slice bound for a given IndexSpan.

NOTE: If the last step is on zero and the stride is negative, this just doesn't work.
OTOH, if the last step is greater than zero then anything between the last step (exclusive) and
the (last + 1) step (inclusive), this is a suitable bound. Since the last step is nonnegative,
min(0, (last + 1) step) works whenever the last step is nonzero and it is impossible
if the last step is zero. -/
def extreme (s : IndexSpan) : Nat := Int.toNat <| s.start + s.num * s.step

/-- Characterizes an IndexSpan can be converted into a slice, ie, when (ie IndexSpan.extreme)
works as an ending bounds.  The num=0 and num=1 cases will be handled separately so they are
excluded here. -/
def isRegular (s : IndexSpan) : Bool := 1 < s.num && 0 < s.start + s.step * (s.num - 1)
def RegularWF (s : IndexSpan) : Prop := s.isRegular

/-- Convert a span to a slice. This encoding is correct when the slice is regular. -/
def regularToSlice (s : IndexSpan) : Slice :=
  ⟨s.start, s.extreme, s.step, s.step_nz⟩

/- A common family of cases for regular slices -/
theorem indexSpan_pos_step_isRegular {s : IndexSpan} (Hstep : 0 < s.step) (Hnum : 1 < s.num) :
    s.isRegular := by
  simp only [isRegular, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨Hnum, ?_⟩
  refine Int.add_pos_of_nonneg_of_pos (Int.ofNat_zero_le s.start) ?_
  refine Int.mul_pos Hstep ?_
  omega

/-- In some cases where the normal formula doesn't work, we can still compile
an IndexSpan to a slice. Namely, if the IndexSpan has zero or one elements, it can
always be compiled by taking steps of size 1 in the positive direction. -/
def isSubsingleton (s : IndexSpan) : Bool := s.num <= 1
def SubsingletonWF (s : IndexSpan) : Prop := s.isSubsingleton
def subsingletonToSlice (s : IndexSpan) : Slice :=
  ⟨s.start, s.start + s.num, 1, Int.zero_ne_one.symm⟩

/-- Attempt to compile an IndexSpan to a slice. -/
def toSlice (s : IndexSpan) : Err Slice :=
  if s.isSubsingleton then .ok s.subsingletonToSlice else
  if s.isRegular then .ok s.regularToSlice else
  .error "Cannot compile IndexSpan to slice"

/-- The span [0, d) -/
def full (d : Nat) : IndexSpan := ⟨0, 1, d, Int.zero_ne_one.symm, by simp; exact fun _ H _ => H⟩


/- ## Composition of two IndexSpans

An IndexSpan `(s1.comp s2)[i] = s1(s2[i])`

This composition uses clipping semantics, ie, it always returns an IndexSpan which
does "as much of (s1.comp s2) as possible". If starting out of bounds, the resulting
`num` field will be zero. -/

namespace comp

variable (s1 s2 : IndexSpan)

@[simp] def start : Int := s1.step * s2.start + s1.start
@[simp] def step : Int := s1.step * s2.step

/-- Means that `i.toNat` is an inbounds access of the IndexSpan `s`. -/
def inbounds? (s : IndexSpan) (i : Int) : Bool := 0 ≤ i && i < s.num


/-- Calculate the number of values i (starting at 0) such that `start + step  * i` is both
nonnegative and less than s2.bound. This will be the maximum (clipped) number of steps
that the composed IndexSpan can take.

TODO: There is a closed form for this, but for now we just explicitly search for the
maximum over all possible indices for s2. -/

@[simp] def num : Nat := List.lenMaxPrefix (List.range s2.num) (inbounds? s1 ∘ s2.get! ∘ Int.ofNat)

/-- Lemma to deal with the Int.toNat coercion in IndexSpan.clipComp -/
theorem start_neg_implies_num_zero (H : start s1 s2 < 0) : comp.num s1 s2 = 0 := by
  apply Nat.eq_zero_of_not_pos; intro H'
  rcases (List.lenMaxPrefix_gt_zero_head H') with ⟨l, L, ⟨H1, H2⟩⟩
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
  apply Nat.le_trans List.lenMaxPrefix_le_length
  rw [List.length_range]
  exact s2.num.le_refl

theorem get!_eq_comp : ∀ i : Int, start s1 s2 + step s1 s2 * i = s1.get! (s2.get! i) := by
  intro i
  simp [start, step, get!]
  conv=> lhs; rw [Int.add_assoc, Int.add_comm, Int.add_assoc]
  congr
  rw [Int.add_comm, Int.mul_add]
  congr 1
  apply Int.mul_assoc

end comp

-- /-- Defines a clipped composition operator for IndexSpans -/
-- def clipComp (s1 s2 : IndexSpan) : IndexSpan where
--   start := Int.toNat <| comp.start s1 s2
--   step := comp.step s1 s2
--   num := comp.num s1 s2
--   step_nz := Int.mul_ne_zero_iff.mpr ⟨s1.step_nz, s2.step_nz⟩
--   get_nonneg i Hlb Hub := by
--     rcases Decidable.em (0 ≤ (comp.start s1 s2)) with (H|H)
--     · rw [Int.ofNat_toNat, Int.max_eq_left H]
--       rw [comp.get!_eq_comp]
--       apply s1.get_nonneg _ _
--       · suffices comp.inbounds? s1 (s2.get! i) by
--           simp [comp.inbounds?] at this
--           apply this.2
--         unfold comp.num at Hub
--         have Hnum := @List.lenMaxPrefix_prefix_holds _ (List.range s2.num)
--                        (comp.inbounds? s1 ∘ s2.get! ∘ Int.ofNat)
--                        i.toNat ?G1 ((Int.toNat_lt Hlb).mpr Hub)
--         case G1 =>
--           apply Nat.lt_of_lt_of_le ((Int.toNat_lt Hlb).mpr Hub)
--           exact List.lenMaxPrefix_le_length
--         simp at Hnum
--         apply (Int.max_eq_left Hlb ▸ Hnum)
--       · apply s2.get_nonneg _ Hlb
--         apply Int.lt_of_lt_of_le Hub
--         apply Int.ofNat_le.mpr
--         exact comp.num_le_ub s1 s2
--     · simp only [comp.start, Int.not_le] at H
--       have _ := comp.start_neg_implies_num_zero (H := H)
--       omega
--
-- @[simp] def clipComp.wf (s1 s2 : IndexSpan) : Prop := 0 ≤ comp.start s1 s2
--
-- /-- As long as the composition is well-defined -/
-- theorem clipComp.get!_eq (s1 s2 : IndexSpan) {i} (Hwf : clipComp.wf s1 s2) :
--     (clipComp s1 s2).get! i = s1.get! (s2.get! i) := by
--   rw [← comp.get!_eq_comp]
--   simp [clipComp]
--   exact Int.max_eq_left Hwf

end IndexSpan

/- ## Layouts -/

/-- Algebraic representation of an affine function taking Int^dim to Int -/
structure Layout (dim : Nat) where
  offset  : Nat
  steps : List Int
  nums    : List Nat
  steps_dim : steps.length = dim
  nums_dim : nums.length = dim
  deriving Repr

/-- An element of ℕ^dim -/
structure Coord (d : Nat) where
  coords : List Int
  coords_dim : coords.length = d

/-- Every element of a Coord is inside the bounds of a particular shape -/
def Coord.inbounds? (s : Shape) (c : Coord s.freeDim) : Prop :=
  (List.zip c.coords s.freeDims).Forall (fun (i, n) => 0 ≤ i ∧ i < n)

/-- Look up a memory coordinate in a layout, without doing any bounds checks -/
def Layout.get! {d} (l : Layout d) (c : Coord d) : Int := l.offset + l.steps.dot c.coords

/-- A list of IndexSpans with a given dimension -/
structure FreeSpans (d : Nat) where
  spans : List IndexSpan
  spans_dim : spans.length = d

def FreeSpans.get! {d : Nat} (f : FreeSpans d) (c : Coord d) : Coord d where
  coords := List.zipWith (IndexSpan.get! · ·) f.spans c.coords
  coords_dim := by simp [FreeSpans.spans_dim, Coord.coords_dim]

/- ## Composition -/

namespace lcomp

def offset {d} (f : FreeSpans d) (l : Layout d) : Int :=
  l.offset + l.steps.dot (f.spans.map (Int.ofNat ∘ IndexSpan.start))

def steps {d} (f : FreeSpans d) (l : Layout d) : List Int :=
  List.zipWith (· * ·) (f.spans.map IndexSpan.step) l.steps

structure wf {d} (f : FreeSpans d) (l : Layout d) : Prop where
  offset_nonneg : 0 ≤ offset f l

def comp {d} (f : FreeSpans d) (l : Layout d) : Layout d where
  offset := Int.toNat <| offset f l
  steps := steps f l
  nums  := l.nums
  steps_dim := by simp [FreeSpans.spans_dim, Layout.steps_dim, steps]
  nums_dim := l.nums_dim

end lcomp

/-- Correctness for span/layout composition
Note that this one says nothing about staying inbounds -/
theorem comp_get {d} (f : FreeSpans d) (l : Layout d) {c : Coord d} (Hwf : lcomp.wf f l):
    (lcomp.comp f l).get! c = l.get! (f.get! c) := by
  simp [lcomp.comp, Layout.get!, Int.max_eq_left Hwf.offset_nonneg]
  unfold lcomp.offset
  rw [Int.add_assoc]; congr 1
  simp [FreeSpans.get!]
  simp [lcomp.steps]
  rcases f with ⟨L1, HL1⟩
  rcases c with ⟨L2, HL2⟩
  rcases l with ⟨L4, L3, L5, HL3, HL4⟩
  simp_all
  clear Hwf HL4 L4
  revert L1 L3 d
  induction L2
  · simp
    intro d L1 HL1 Hd L3 HL3; subst Hd
    simp_all [List.dot]
  · simp
    rename_i l2 L2 IH
    intro d L1 HL1 Hd L3 HL3; subst Hd
    rcases L1 with _ | ⟨l1, L1⟩ ; simp at HL1
    rcases L3 with _ | ⟨l3, L3⟩ ; simp at HL3
    simp_all [List.dot]
    -- Move non-recursive terms to the left
    conv=>
      lhs
      rw [← Int.add_assoc]
      enter [1]
      rw [Int.add_assoc]
      rw [Int.add_comm _ (_ * _ * _)]
      rw [← Int.add_assoc]
    conv=>
      lhs
      rw [Int.add_assoc]
    -- Solve recursive and non-recursive case separately
    congr 1
    · rw [Int.mul_add]; congr 1
      rw [← Int.mul_assoc, Int.mul_comm l3 _]
    · exact IH L1 HL1 rfl _ HL3


/-- NOTE:

For this reason, we impose an error semantics instead. -/


/- ## Span Semantics -/

abbrev LayoutMap d := Layout d → Layout d

def coordToIndexSpan (x : Nat) : IndexSpan where
  start := x
  step := 1
  num := 1
  step_nz := Int.zero_ne_one.symm
  get_nonneg := by simp; omega

def Slice.toIndexSpan (s : Slice) (size : Nat) : IndexSpan where
  start := s.l
  step := s.step
  num := min size s.size
  step_nz := s.wf
  get_nonneg i := by
    suffices 0 ≤ i → i < ↑s.size → 0 ≤ ↑s.l + s.step * i by
      intro H1 H2; apply this H1
      apply Int.lt_of_lt_of_le H2
      apply Int.ofNat_le.mpr
      exact Nat.min_le_right size s.size
    simp [Slice.size]
    split <;> intros Hlb Hub
    · apply Int.le_add_of_neg_add_le_right
      rw [Int.neg_mul_eq_neg_mul, Int.add_zero]
      rw [← Int.toNat_of_nonneg Hlb] at Hub
      rw [Int.mul_comm]
      apply Int.mul_le_of_le_ediv; omega
      rw [← Int.max_eq_left Hlb, ← Int.ofNat_toNat]
      apply Int.le_trans (Int.le_of_lt Hub)
      rw [Int.natCast_ediv]
      apply Int.le_ediv_of_mul_le; omega
      have R1 : ↑s.step.natAbs = -s.step := by
        apply Int.ofNat_natAbs_of_nonpos; omega
      rw [R1]; clear R1
      apply Int.le_trans
      · apply Int.mul_le_mul_of_nonneg_right
        · apply Int.ediv_le_ediv
          · omega
          · apply Int.ofNat_le.mpr
            exact Nat.sub_le s.l s.u
        · omega
      apply Int.mul_le_of_le_ediv; omega
      apply Int.le_refl
    · rename_i h
      apply Int.add_nonneg (Int.ofNat_zero_le s.l)
      apply Int.mul_nonneg (Int.not_lt.mp h) Hlb

def Index.toIndexSpan (i : Index) (size : Nat) : IndexSpan :=
  match i with
  | .coord x => coordToIndexSpan x
  | .slice s => s.toIndexSpan size
  | .dynamic _ => .full size -- NOTE: do we need to fix clipping?

def simpleInterpPar (t : TensorName) : IndexSpan :=
  .full t.shape.parDim

def simpleInterpFree (t : TensorName) : LayoutMap t.freeDim :=
  let F : FreeSpans t.freeDim := ⟨t.shape.freeDims.map .full, by simp⟩
  lcomp.comp F

def basicInterpPar (b : AccessBasic) : IndexSpan :=
  b.parIndex.toIndexSpan b.getShape.parDim

def basicInterpFree (b : AccessBasic) : LayoutMap b.freeDim :=
  let F : FreeSpans b.freeDim := FreeSpans.mk
    (List.zipWith (·.toIndexSpan ·) b.freeIndices b.getShape.freeDims)
    (by
      rcases b with ⟨_, L, Hwf⟩
      simp [AccessBasic.getShape, AccessBasic.shape]
      apply Nat.min_eq_right
      cases L
      · simp at Hwf
      · simp)
  lcomp.comp F

def patternInterpPar (p : AccessPattern) : IndexSpan :=
  .full p.parNum

def patternInterpFree (p : AccessPattern) : LayoutMap p.freeDim := fun l =>
  let coeff_sum : Int := (p.freePattern.map APPair.step).sum
  Layout.mk
    (p.freeOffset + coeff_sum * l.offset).toNat
    (l.steps.map (coeff_sum * ·))
    (p.freePattern.map APPair.num)
    (by rw [List.length_map]; exact l.steps_dim)
    (by simp [List.length_map, AccessPattern.freeDim, AccessPattern.shape])

def Access.interpPar : Access → IndexSpan
| .simple s => simpleInterpPar s
| .basic b => basicInterpPar b
| .pattern p => patternInterpPar p
| .birPattern _ => panic! "bir pattern in indexing" -- TODO

def Access.interpFree : (a : Access) → LayoutMap a.freeDim
| .simple s => simpleInterpFree s
| .basic b => basicInterpFree b
| .pattern p => patternInterpFree p
| .birPattern _ => fun x => x -- TODO

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
def CompileIndex.freePairs (t : TensorName) (parNum : Nat) (l : Layout d) : AccessPattern where
  tensor := t
  parNum := parNum
  freePattern := List.zipWith APPair.mk l.steps l.nums
  freeOffset := l.offset

def Layout.rowMajorForm (s : Shape) : Layout s.freeDim where
  offset := 0
  steps := s.freeDims.tails'.map <| Int.ofNat ∘ natListProd
  nums := s.freeDims
  steps_dim := by simp
  nums_dim := by simp


def TensorName.toAP (a : TensorName) : KLR.Err AccessPattern := do
  let layout := a.shape.toList
  let steps := layout.tail ++ [1]
  let steps := steps.scanr (· * ·) 1 |>.dropLast
  return {
    tensor := a
    parNum := layout[0]!
    freePattern := (List.zip steps layout).tail.map (fun (step, size) => ⟨step, size⟩)
    freeOffset := 0
  }

private def getTensorName (shape : List Nat) : Err TensorName :=
  let addr : Address := {
    name := "A", memory := .sbuf,
    parSize := 4, freeSize := 24,
    parOffset := none, freeOffset := none
  }
  let t := TensorName.make "A" .int8 (.mk shape.head! shape.tail!) addr
  match t with
  | .ok t => .ok t
  | .error err => .error err

#guard (do
  let t <- getTensorName [4,3,2]
  let ac <- TensorName.toAP t
  let bir := BirAccessPattern.fromAccessPattern ac
  .ok (bir.pattern, bir.offset)) == .ok ([⟨6,4⟩, ⟨2,3⟩, ⟨1,2⟩], 0)

#guard (do
  let t <- getTensorName [4,3]
  let ac <- TensorName.toAP t
  let bir := BirAccessPattern.fromAccessPattern ac
  .ok (bir.pattern, bir.offset)) == .ok ([⟨3,4⟩, ⟨1,3⟩], 0)


def AccessBasic.idx_sz_and_offset (idxs : List Index) : List (Int × Int) :=
  idxs.map (fun idx =>
      match idx with
      | .coord c => (1, c)
      | .slice s => (((s.u - s.l) / s.step), min s.l s.u)
      | .dynamic d => (d.size, d.offset)) -- TODO:(pavel) verify

def idxToAp (layout : List Nat) (idxs : List Index) : (List APPair ×  Nat) :=
  let steps := layout.tail ++ [1] -- step for dim 0 is 1 and the rest is prev dim
  let steps := steps.scanr (· * ·) 1 |>.dropLast -- actual step is accum of all prev step sizes
  let sz_off := AccessBasic.idx_sz_and_offset idxs -- get all index size and offset
  let sz := sz_off.map (·.1.toNat)
  let off := sz_off.map (·.2)
  let totalOff := List.sum (List.zip off steps |>.map (fun (o, s) => o.toNat * s))
  let pairs : List APPair :=  (List.zip steps sz).map (fun (st, sz) => ⟨ st, sz ⟩)
  (pairs, totalOff)

def AccessBasic.toAP (a : AccessBasic) : KLR.Err AccessPattern := do
  let layout := a.tensor.shape.toList
  let (pairs, offset) := idxToAp layout a.indexes
  return {
    tensor := a.tensor
    parNum := pairs[0]!.num
    freePattern := pairs.tail
    freeOffset := offset
  }

private def testAccess (idxs : List Index) : KLR.Err (List APPair × Nat) := do
  let addr : Address := {
    name := "A", memory := .sbuf,
    parSize := 4, freeSize := 24,
    parOffset := none, freeOffset := none
  }
  let t <- TensorName.make "A" .int8 (.mk 4 [3, 2]) addr
  let ac <- AccessBasic.make t idxs
  match AccessBasic.toAP ac with
  | .ok ac =>
    let bir := BirAccessPattern.fromAccessPattern ac
    .ok (bir.pattern, bir.offset)
  | .error e => .error e

#guard testAccess
 [.coord 0, .coord 0, .coord 0] ==
  .ok ([⟨6,1⟩, ⟨2,1⟩, ⟨1,1⟩], 0)
#guard testAccess
 [.coord 0, .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)] ==
  .ok ([⟨6,1⟩, ⟨2,3⟩, ⟨1,2⟩], 0)
#guard testAccess
 [.coord 1, .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)] ==
  .ok ([⟨6,1⟩, ⟨2,3⟩, ⟨1,2⟩], 6)
#guard testAccess
 [.slice (Slice.make! 1 3 1), .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,2⟩, ⟨2,3⟩, ⟨1,2⟩], 6)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .coord 0, .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,4⟩, ⟨2,1⟩, ⟨1,2⟩], 0)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .coord 1, .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,4⟩, ⟨2,1⟩, ⟨1,2⟩], 2)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .slice (Slice.make! 1 3 1), .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,4⟩, ⟨2,2⟩, ⟨1,2⟩], 2)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .slice (Slice.make! 0 3 1), .coord 0] ==
 .ok ([⟨6,4⟩, ⟨2,3⟩, ⟨1,1⟩], 0)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .slice (Slice.make! 0 3 1), .coord 1] ==
 .ok ([⟨6,4⟩, ⟨2,3⟩, ⟨1,1⟩], 1)

def AccessPattern.toAP (a : AccessPattern) : KLR.Err AccessPattern :=
  .ok a

def Access.toAP (a : Access) : KLR.Err AccessPattern :=
  match a with
  | .simple s => TensorName.toAP s
  | .basic b => AccessBasic.toAP b
  | .pattern p => .ok p
  | .birPattern _ => throw "Converting birAP to AP is lossy"

def Access.combine (a : Access) (idx : List Index) : KLR.Err AccessPattern := do
  for i in idx do
    match i with
    -- This is probably artificial. We need to test combine better with stride != 1
    -- until this check can be dropped
    | .slice s =>
      if s.step != 1 then
        throw "can't combine indecies with stride != 1"
    | _ => pure ()
  let shape := <- a.shape
  let ap <- Access.toAP a
  let pat1 := ⟨ap.freeDim, ap.parNum⟩ :: ap.freePattern
  let off1 := ap.freeOffset
  let (pat2, off2) := idxToAp shape.toList idx
  let pairs := List.zipWith (fun p1 p2 => ⟨max p1.step p2.step, min p1.num p2.num⟩) pat1 pat2
  let offset := off1 + off2
  return {
    tensor := ap.tensor
    parNum := pairs[0]!.num
    freePattern := pairs.tail
    freeOffset := offset
  }

private def testAccess2 (idxs1 : List Index) (idxs2 : List Index) : KLR.Err (List APPair × Nat) := do
  let addr : Address := {
    name := "A", memory := .sbuf,
    parSize := 4, freeSize := 24,
    parOffset := none, freeOffset := none
  }
  let t <- TensorName.make "A" .int8 (.mk 4 [3, 2]) addr
  let ab <- AccessBasic.make t idxs1
  let ac <- AccessBasic.toAP ab
  let ac2 <- Access.combine (.pattern ac) idxs2
  let bir := BirAccessPattern.fromAccessPattern ac2
  .ok (bir.pattern, bir.offset)

#guard testAccess2
    [.slice (Slice.make! 1 2 1), .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)]
    [.coord 0, .slice (Slice.make! 0 3 1), .coord 0] ==
    .ok ([⟨6,1⟩, ⟨2,3⟩, ⟨1,1⟩], 6)
#guard testAccess2
    [.slice (Slice.make! 1 2 1), .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)]
    [.coord 0, .slice (Slice.make! 1 2 1), .slice (Slice.make! 0 2 1)] ==
    .ok ([⟨6,1⟩, ⟨2,1⟩, ⟨1,2⟩], 8)
#guard testAccess2
    [.slice (Slice.make! 1 3 1), .slice (Slice.make! 1 3 1), .slice (Slice.make! 0 2 1)]
    [.slice (Slice.make! 0 2 1), .slice (Slice.make! 0 2 1), .coord 1] ==
     .ok ([⟨6,2⟩, ⟨2,2⟩, ⟨1,1⟩], 9)



end KLR.Core
