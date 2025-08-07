/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.DFrac
import Iris.Instances.heProp

/-- Prop-Valued version of `Option.isSome`; easier to do cases on. -/
inductive Option.IsSomeP : Option α → Prop where
| some : IsSomeP (some v)

theorem Option.isSomeP_iff_isSome {v : Option α} : v.IsSomeP ↔ v.isSome = true := by
  constructor
  · rintro ⟨⟩; rfl
  · cases v <;> rintro ⟨⟩; exact Option.IsSomeP.some

def List.forall {α : Type _} (L : List α) (P : α → Prop) : Prop :=
  match L with
  | .nil => True
  | .cons ll L => P ll ∧ List.forall L P

def List.dot' [Mul α] [Add α] [Zero α] (L1 L2 : List α) : α :=
  (List.zipWith (· * ·) L1 L2).sum

class Encodable (dsize : Nat) (α β : Type _) where
  read : Vector α dsize → Option β
  write : β → Vector α dsize
  read_write : (read v).map write = .none ∨ (read v).map write = .some v
  write_read : read (write b) = .some b

instance self_encoding {α : Type _} : Encodable 1 α α where
  read v := v[0]
  write v := .mk #[v] (by simp)
  read_write {v} := by
    simp only [Option.map_some, reduceCtorEq, Option.some.injEq, Vector.mk_eq, false_or]
    ext; simp
    rename_i i _ _
    suffices i = 0 by simp [this]
    simp_all
  write_read := by simp

abbrev PNat := { n : Nat // 0 < n }
@[simp] def PNat.add (n1 n2 : PNat) : PNat := ⟨n1.1 + n2.1, Nat.add_pos_left n1.2 _⟩
@[simp] def PNat.one : PNat := ⟨1, Nat.one_pos⟩


-- TODO: Upstream this entire section

section iris_lib
open Iris

instance : UFraction PNat where
  Proper n := n.1 = 1
  add := PNat.add
  add_comm := by
    rintro ⟨n1, _⟩ ⟨n2, _⟩; ext
    have _ := Nat.add_comm n1 n2
    simp_all [HAdd.hAdd, PNat.add]
  add_assoc := by
    rintro ⟨n1, _⟩ ⟨n2, _⟩ ⟨n3, _⟩; ext
    have _ := Nat.add_assoc n1 n2 n3
    simp_all [HAdd.hAdd, PNat.add]
  add_left_cancel := by
    rintro ⟨n1, _⟩ ⟨n2, _⟩ ⟨n3, _⟩ H
    have _ : n1 + n2 = n1 + n3 → n2 = n3 := (Nat.add_left_cancel ·)
    simp_all [HAdd.hAdd, PNat.add]
  add_ne := by
    rintro ⟨n1, _⟩ ⟨n2, _⟩
    have _ : n1 ≠ n2 + n1 := by omega
    simp_all [HAdd.hAdd, PNat.add]
  proper_add_mono_left := by
    rintro ⟨n1, _⟩ ⟨n2, _⟩
    have _ : n1 + n2 = 1 → n1 = 1 := by omega
    simp_all [HAdd.hAdd, PNat.add]
    trivial
  one := PNat.one
  one_whole := by
    simp [Fraction.Whole, Subtype, Fraction.Fractional, Subtype.val]
    constructor
    · rfl
    · simp_all [Subtype.val, One.one, HAdd.hAdd, PNat.add, PNat.one, One.toOfNat1, OfNat.ofNat]
      intro n
      simp [Subtype.val, One.one, HAdd.hAdd, PNat.add]
      intro x H
      have _ : (1 + n = 1) := H
      omega

/-- Generic UPred adequacy theorem: If one can prove a pure proposition under some valid model, then
the pure proposition holds. -/
theorem UPred.soundness_pure_gen [UCMRA A] {a : A} (Hv : ✓{n} a) : (UPred.ownM a ⊢ ⌜P⌝) → P :=
  (· _ a Hv (CMRA.incN_refl a))

theorem UPred_adequacy_later_gen [UCMRA A] {a : A} (Hv : ✓ a) (P : UPred A) :
    (UPred.ownM a ⊢ ▷ P) → (UPred.ownM a ⊢ P) := by
  intro HP n x Hx H
  refine UPred.mono _ ?_ H n.le_refl
  exact HP n.succ _ (CMRA.Valid.validN Hv) (CMRA.incN_refl a)

theorem UPred_adequacy_laterN_gen [UCMRA A] {a : A} (Hv : ✓ a) (P : UPred A) :
    (UPred.ownM a ⊢ ▷^[N] P) → (UPred.ownM a ⊢ P) := by
  intro H
  induction N <;> simp_all [BI.BIBase.laterN]
  rename_i IH
  exact IH <| UPred_adequacy_later_gen Hv _ H

theorem UPred.all_absorbing [UCMRA A] (P : UPred A) : Iris.BI.Absorbing P where
  absorbing := by
    intro n x Hx
    simp [Iris.BI.absorbingly, BI.sep, BI.pure, UPred.sep, UPred.pure]
    intro x1 x2 Hx1x2 H
    refine P.mono H ?_ ?_
    · exists x1
      apply Hx1x2.trans
      apply CMRA.op_commN
    · apply n.le_refl

theorem bupd_soundness [UCMRA M] (P : UPred M) [Iris.BI.Plain P] : (⊢ |==> P) → ⊢ P := (·.trans bupd_elim)

theorem bupd_gen_soundness [UCMRA M] (P : UPred M) [Iris.BI.Plain P] (R : UPred M) : (R ⊢ |==> P) → R ⊢ P := by
  intro H
  apply H.trans
  apply bupd_elim

-- TODO This is more general than UPred M and I think it is ⊣⊢
theorem plainly_laterN [UCMRA M] (P : Prop) : iprop((■ ▷^[n]⌜P⌝ : UPred M) ⊢ ▷^[n]■ ⌜P⌝) := by
  induction n <;> simp [BI.BIBase.laterN]
  rename_i n IH
  apply BIPlainly.later_plainly.mpr.trans
  exact BI.later_mono IH

theorem laterN_mono [UCMRA M] {P Q : UPred M} : (P ⊢ Q) → ▷^[n] P ⊢ ▷^[n] Q := by
  induction n <;> simp [BI.BIBase.laterN]
  intro H
  rename_i h
  exact BI.later_mono (h H)

theorem later_bupd_comm_pure [UCMRA M] {P : Prop} : iprop(▷ |==> (⌜P⌝ : UPred M) ⊢ |==> ▷ ⌜P⌝) := by
  intro n x Hx
  simp [bupd, UPred.bupd, BI.pure, UPred.pure, BI.later, UPred.later]
  intro H k yf Hkn Hx'
  refine ⟨⟨_, Hx'⟩, ?_⟩
  rcases n with (_|n''); simp_all
  simp at H
  split; trivial
  rename_i n1 n2
  have H' := H n2 yf (Nat.le_of_lt_succ Hkn) (CMRA.validN_succ Hx')
  exact H'.2

theorem later_bupd_comm_plain [UCMRA M] {P : UPred M} [Iris.BI.Plain P] : iprop(▷ |==> P ⊢ |==> ▷ P) := by
  suffices (BI.later iprop(|==> plainly P) ⊢ |==> BI.later (plainly P)) by
    refine (BI.later_mono <| BIUpdate.mono BI.Plain.plain).trans ?_
    refine this.trans (BIUpdate.mono <| BI.later_mono BI.plainly_elim )
  intro n x Hx
  simp [bupd, UPred.bupd, plainly, UPred.plainly, BI.later, UPred.later]
  intro H k yf Hkn Hx'
  refine ⟨⟨_, Hx'⟩, ?_⟩
  rcases n with (_|n''); simp_all
  simp at H
  split; trivial
  rename_i n1 n2
  have H' := H n2 yf (Nat.le_of_lt_succ Hkn) (CMRA.validN_succ Hx')
  exact H'.2

instance later_plainly [UCMRA M] {P : UPred M} [Iris.BI.Plain P] : Iris.BI.Plain iprop(▷ P) where
  plain := by
    refine .trans (BI.later_mono Iris.BI.Plain.plain) ?_
    exact fun n x a a => a

instance laterN_plainly [UCMRA M] {P : UPred M} [Iris.BI.Plain P] : Iris.BI.Plain iprop(▷^[n] P) where
  plain := by
    induction n with | zero => ?_ | succ n IH => ?_
    · simp [BI.BIBase.laterN]
      exact Iris.BI.Plain.plain
    · simp [BI.BIBase.laterN]
      refine .trans (BI.later_mono IH) ?_
      exact fun n_1 x a a => a

instance pure_plain [UCMRA M] {P : Prop}  : Iris.BI.Plain iprop(⌜P⌝ : UPred M) where
  plain := by exact fun n x a a => a

theorem laterN_intro [UCMRA M] {P : UPred M} : iprop(P ⊢ ▷^[n] P) := by
  induction n with | zero => ?_ | succ n IH => ?_
  · simp [BI.BIBase.laterN]
  · exact .trans BI.later_intro (BI.later_mono IH)

theorem bupd_ownM_updateP [UCMRA M] (Φ : M → Prop) :
    x ~~>: Φ → UPred.ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ UPred.ownM y := by
  intro Hup
  rintro n x2 _ ⟨x3, Hk⟩ k yf _ Hv
  have G : ✓{k} x •? some (x3 • yf) := by
    simp [CMRA.op?]
    apply CMRA.validN_ne _ Hv
    refine .trans ?_ CMRA.assoc.dist.symm
    refine CMRA.op_commN.trans (.trans ?_ CMRA.op_commN)
    apply CMRA.op_ne.ne
    apply OFE.Dist.le Hk
    trivial
  obtain ⟨y, _, _⟩ := Hup k (some (x3 • yf)) G
  exists (y • x3)
  refine ⟨?_, ?_⟩
  · rename_i Hy
    simp [CMRA.op?] at Hy
    apply CMRA.validN_ne _ Hy
    refine .trans ?_ CMRA.assoc.dist
    exact CMRA.op_ne.ne .rfl
  · simp [BI.exists, BI.sExists, UPred.sExists]
    exists (UPred.ownM y)
    refine ⟨?_, ?_⟩
    · exists y
      refine UPred.ext_iff.mpr ?_
      apply funext (fun n => funext fun x => ?_)
      simp [BI.pure, BI.and, UPred.and, UPred.pure]
      intro _
      trivial
    · exists x3

end iris_lib

/- TODO : Upstream
/-- Composition of Heaps
NB. Potentially dangerous instance. -/
instance instHeapComp [Heap T K1 T'] [Heap T' K2 V] : Heap T (K1 × K2) V where
  get h k := Store.get h k.1 |>.bind (Store.get · k.2)
  set h k v := Store.set h k.1 (some <| Store.set (Store.get h k.1 |>.getD Heap.empty) k.2 v)
  empty := Heap.empty
  hmap f h := Heap.hmap (fun k1 t1 => some <| Heap.hmap (fun k2 v => f (k1, k2) v) t1) h
  merge op x y := Heap.merge (Heap.merge op) x y
  get_set_eq {t k k' v} H := by cases k' <;> cases k <;> simp_all [Store.get_set_eq]
  get_set_ne {t k k' v} H := by
    cases k' <;> cases k <;> simp [Store.get_set_ne, Option.bind]
    rename_i i1 j1 i2 j2
    if hi : i2 = i1
      then if hj : j1 = j2 then exfalso; simp_all
           else
             simp [Store.get_set_eq hi]
             cases _ : (Store.get t i2) <;>
             simp_all [Option.getD, Store.get_set_ne, Heap.get_empty]
      else rw [Store.get_set_ne hi]
  get_empty {k} := by cases k <;> simp_all [Heap.get_empty]
  get_hmap {f t k} := by
    simp [Heap.get_hmap]
    cases (Store.get t k.fst) <;> simp [Store.get, Heap.hmap, Heap.get_hmap]
  get_merge {op x y} k := by
    rename_i i j
    simp [hmap, Heap.get_merge, Option.merge]
    cases _ : Store.get x k.fst  <;>
    cases _ : Store.get y k.fst <;>
    simp_all [Heap.get_merge] <;>
    grind

-/

/-- A multiaffine equation describing an access into a free coordinate of an Address -/
structure AffineMap where
  free_offset : Int
  free_strides : List Int
  par_offset : Int
  par_stride : Int
  deriving Repr, BEq

def AffineMap.par (a : AffineMap) (i : Int) : Int :=
  a.par_offset + a.par_stride * i

def AffineMap.free (a : AffineMap) (i : List Int) : Int :=
  a.free_offset + List.dot' a.free_strides i

def AffineMap.is_trivial (a : AffineMap) : Prop :=
  a.free_offset = 0 ∧
  a.par_offset = 0 ∧
  a.par_stride = 1 ∧
  a.free_strides = a.free_strides.map (fun _ => 1)

theorem Iris.BI.BIBase.Entails.trans' {PROP : Type _} [BI PROP] {P Q R : PROP} (h2 : Q ⊢ R) (h1 : P ⊢ Q) : P ⊢ R :=
  h1.trans h2

