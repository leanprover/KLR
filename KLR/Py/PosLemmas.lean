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

/-! # Lemmas used to prove progress in the tokenizer -/

set_option grind.warning false

abbrev PosGe (pos : String.Pos) :=
  {endPos : String.Pos // endPos.1 ≥ pos.1}

abbrev PosGt (pos : String.Pos) :=
  {endPos : String.Pos // endPos.1 > pos.1}

def PosGt.next' {s : String} (pos : String.Pos) (h : ¬s.atEnd pos = true)
  : PosGt pos :=
  ⟨s.next' pos h, by grind [String.pos_lt_eq, String.lt_next', String.next'_eq]⟩

def PosGt.fromNext' {s : String} {pos : String.Pos}
  (h : ¬s.atEnd pos = true) (next : PosGt (s.next' pos h)) : PosGt pos :=
  ⟨next.val, by grind [String.pos_lt_eq, String.lt_next', String.next'_eq]⟩

def PosGt.fromLe {pos1 pos2 : String.Pos}
  (h : pos1.1 ≤ pos2.1) (posGt : PosGt pos2) : PosGt pos1 :=
  ⟨posGt.val, by grind⟩

theorem String.lt_end {s : String} {pos : String.Pos} (h : ¬s.atEnd pos = true)
  : pos.1 < s.endPos.1 := by
  simp only [String.atEnd, ge_iff_le, decide_eq_true_eq, Nat.not_le] at h
  exact h

theorem String.lt_sub_next {s : String} {pos : String.Pos} (h : ¬s.atEnd pos = true)
  : s.endPos.1 - (s.next' pos h).1 < s.endPos.1 - pos.1 := by
  have hlt := String.lt_next' s pos
  have heq := String.next'_eq _ _ h
  have := String.lt_end h
  rw [heq]
  simp_all only [pos_lt_eq, next'_eq, gt_iff_lt]
  omega

theorem String.findAux_le_start {s : String} {p : Char → Bool} {stopPos pos : String.Pos}
  : pos.1 ≤ (s.findAux p stopPos pos).1 := by
  rw [String.findAux]
  split
  next h =>
    split
    · grind
    · simp only
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      have := @String.findAux_le_start s p stopPos (s.next pos)
      grind
  · grind
termination_by stopPos.1 - pos.1

theorem String.add_gt
  : ∀ {pos : String.Pos} {s : String},
    s.utf8ByteSize > 0 → (pos + s).byteIdx > pos.byteIdx := by
  intro pos s h
  simp_all only [Bool.not_eq_true, gt_iff_lt, String.Pos.byteIdx_addString, Nat.lt_add_right_iff_pos]

/--
Tries to solve theorems of the form `s.utf8ByteSize > n`.
-/
macro "simp_str_size" : tactic => `(tactic|(
  rw [←String.size_toUTF8]
  simp [String.toUTF8, String.utf8EncodeChar, ByteArray.size]
))
