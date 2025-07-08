/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

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
