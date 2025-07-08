/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.DFrac

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
  | .cons l L => P l ∧ List.forall L P

def List.dot [Mul α] [Add α] [Zero α] (L1 L2 : List α) : α :=
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

section iris_lib
open Iris

instance : DFractional PNat where
  proper n := n.1 = 1
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
  whole_iff_one := by
    rintro ⟨n1, _⟩
    simp_all [whole, Subtype.val, One.one, HAdd.hAdd, PNat.add, PNat.one, One.toOfNat1, OfNat.ofNat]
    intro rfl
    simp [whole, Subtype.val, One.one, HAdd.hAdd, PNat.add]
    intro x H Hk
    cases x
    · exfalso
      omega
    · rename_i n
      obtain ⟨⟩ : (n + 1) = 0 := Nat.left_eq_add.mp Hk.symm

end iris_lib
