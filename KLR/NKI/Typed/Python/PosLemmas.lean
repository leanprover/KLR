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

/-!
# Lemmas used to prove progress in the tokenizer

TODO: Clean this up with better naming convention
-/

abbrev PosGe (startPos : String.Pos) :=
  {endPos : String.Pos // endPos.byteIdx ≥ startPos.byteIdx}

abbrev PosGt (startPos : String.Pos) :=
  {endPos : String.Pos // endPos.byteIdx > startPos.byteIdx}

theorem String.lt_end :
  ∀ (s : String) (pos : String.Pos),
    ¬s.atEnd pos = true → pos.byteIdx < s.endPos.byteIdx := by
  intro s pos h
  simp only [String.atEnd, ge_iff_le, decide_eq_true_eq, Nat.not_le] at h
  exact h

theorem String.lt_sub_next :
  ∀ (s : String) (pos : String.Pos) (h : ¬s.atEnd pos = true),
    (s.endPos - s.next' pos h).byteIdx < (s.endPos - pos).byteIdx := by
  intro s pos h
  have hlt := String.lt_next' s pos
  have heq := String.next'_eq _ _ h
  rw [heq]
  simp_all [LT]
  have := String.lt_end s pos h
  omega

theorem PosGe.lt_of_gt :
  ∀ (s : String) (startPos : String.Pos) (_ : ¬s.atEnd startPos = true) (pge : PosGe startPos),
    pge.val.byteIdx > startPos.byteIdx →
      s.endPos.byteIdx - pge.val.byteIdx < s.endPos.byteIdx - startPos.byteIdx := by
  intro s startPos h pge hgt
  have := String.lt_end s startPos h
  omega

theorem PosGt.lt_sub_next :
  ∀ {pos : String.Pos} {s : String} {h : ¬s.atEnd pos = true} (pos' : PosGt (s.next' pos h)),
    (s.endPos - pos'.val).byteIdx < (s.endPos - pos).byteIdx := by
  intro pos s h pos'
  obtain ⟨pos', hpos'⟩ := pos'
  have hlt := String.lt_next' s pos
  have heq := String.next'_eq _ _ h
  have := String.lt_end s pos h
  simp_all only [String.pos_lt_eq, String.next'_eq, String.Pos.sub_byteIdx, gt_iff_lt]
  simp_all only [String.next'_eq, gt_iff_lt]
  omega

theorem PosGt.lt_start :
  ∀ (startPos : String.Pos) (s : String) (_ : ¬s.atEnd startPos = true) (pos : PosGt startPos),
    (s.endPos - pos.val).byteIdx < (s.endPos - startPos).byteIdx := by
  intro startPos s h pos
  obtain ⟨pos, hpos⟩ := pos
  have hlt := String.lt_next' s pos
  have heq := String.next'_eq _ _ h
  have := String.lt_end s startPos h
  simp_all only [String.pos_lt_eq, String.next'_eq, String.Pos.sub_byteIdx, gt_iff_lt]
  simp_all only [String.next'_eq, gt_iff_lt]
  omega

theorem PosGe.lt_sub_next :
  ∀ {pos : String.Pos} {s : String} {h : ¬s.atEnd pos = true} (pos' : PosGe (s.next' pos h)),
    (s.endPos - pos'.val).byteIdx < (s.endPos - pos).byteIdx := by
  intro pos s h pos'
  obtain ⟨pos', hpos'⟩ := pos'
  have hlt := String.lt_next' s pos
  have heq := String.next'_eq _ _ h
  have := String.lt_end s pos h
  simp_all only [String.pos_lt_eq, String.next'_eq, String.Pos.sub_byteIdx, gt_iff_lt]
  simp_all only [String.next'_eq, gt_iff_lt]
  omega

theorem String.ge_next :
  ∀ (s : String) (pos : String.Pos) (h : ¬s.atEnd pos = true),
    (s.next' pos h).byteIdx ≥ pos.byteIdx := by
  intro s pos h
  have hlt := String.lt_next' s pos
  have heq := String.next'_eq _ _ h
  rw [heq]
  simp_all only [pos_lt_eq, next'_eq, ge_iff_le]
  omega

theorem PosGe.next_gt :
  ∀ {s : String} {pos : String.Pos} {h : ¬s.atEnd pos = true}
    (pge : PosGe (s.next' pos h)), pge.val.byteIdx > pos.byteIdx := by
  intro s pos h pge
  obtain ⟨pos', hpos'⟩ := pge
  have := String.lt_next' s pos
  rw [String.next'_eq _ _ h] at hpos'
  simp_all only [ge_iff_le, String.pos_lt_eq]
  omega

def PosGe.next' {s : String} (pos : String.Pos) (h : ¬s.atEnd pos) : PosGe pos :=
  ⟨s.next' pos h, by
    have := String.lt_next' s pos
    have := String.next'_eq _ _ h
    rw [this] at *
    simp_all only [Bool.not_eq_true, String.pos_lt_eq, ge_iff_le]
    omega
  ⟩

theorem PosGe.next_ge :
  ∀ {s : String} {pos : String.Pos} {h : ¬s.atEnd pos = true}
    (pge : PosGe (s.next' pos h)), pge.val.byteIdx ≥ pos.byteIdx := by
  intro _ _ _ pge
  have := pge.next_gt
  omega

theorem PosGe.next_gt_trans_gt :
  ∀ {s : String} {pos : String.Pos} {h : ¬s.atEnd pos = true}
    {pgt : PosGt (s.next' pos h)}
    (pge : PosGe pgt.val), pge.val.byteIdx > pos.byteIdx := by
  intro s pos h pgt
  obtain ⟨pos', hpos'⟩ := pgt
  have := String.lt_next' s pos
  rw [String.next'_eq _ _ h] at hpos'
  simp_all only [ge_iff_le, String.pos_lt_eq]
  omega

theorem PosGe.next_gt_trans_ge :
  ∀ {s : String} {pos : String.Pos} {h : ¬s.atEnd pos = true}
    {pgt : PosGt (s.next' pos h)}
    (pge : PosGe pgt.val), pge.val.byteIdx ≥ pos.byteIdx := by
  intro s pos h pgt pge
  have := pge.next_gt_trans_gt
  omega

theorem PosGe.ge_next_gt_trans_ge :
  ∀ {s : String} {startPos : String.Pos}
    (pos : PosGe startPos) (h : ¬s.atEnd pos = true)
    (endPos : PosGe (s.next' pos.val h)), endPos.val.byteIdx ≥ startPos.byteIdx := by
  intro s startPos pos h endPos
  obtain ⟨pos, hpos⟩ := pos
  obtain ⟨endPos, hEndPos⟩ := endPos
  have := String.lt_next' s pos
  have := String.next'_eq _ _ h
  rw [this] at hEndPos
  simp_all only [ge_iff_le, String.pos_lt_eq, String.next'_eq]
  omega

theorem PosGe.next_ge_trans_gt :
  ∀ {s : String} {pos : String.Pos} {h : ¬s.atEnd pos = true}
    (pge : PosGe (s.next' pos h))
    (pge' : PosGe pge.val), pge'.val.byteIdx > pos.byteIdx := by
  intro s pos h pge
  obtain ⟨pos', hpos'⟩ := pge
  have := String.lt_next' s pos
  rw [String.next'_eq _ _ h] at hpos'
  simp_all only [ge_iff_le, String.pos_lt_eq]
  omega

theorem PosGe.next_ge_trans_ge :
  ∀ {s : String} {pos : String.Pos} {h : ¬s.atEnd pos = true}
    {pge : PosGe (s.next' pos h)}
    (pge' : PosGe pge.val), pge'.val.byteIdx ≥ pos.byteIdx := by
  intro s pos h pge pge'
  have := pge.next_ge_trans_gt pge'
  omega

theorem PosGe.ge_of_trans_gt :
  ∀ {startPos : String.Pos} {pgt : PosGt startPos} (pge : PosGe pgt.val),
    pge.val.byteIdx ≥ startPos.byteIdx := by
  intro startPos pgt pge
  obtain ⟨pos, hgt⟩ := pgt
  obtain ⟨pos', hge⟩ := pge
  simp_all only [ge_iff_le]
  simp only [ge_iff_le] at hge
  omega

theorem PosGt.gt_of_trans_gt :
  ∀ {startPos : String.Pos} {pge : PosGe startPos} (pgt : PosGt pge),
    pgt.val.byteIdx > startPos.byteIdx := by
  intro startPos pgt pge
  obtain ⟨pos, hgt⟩ := pgt
  obtain ⟨pos', hge⟩ := pge
  simp_all only [ge_iff_le]
  simp_all only [gt_iff_lt]
  omega

theorem PosGt.ge_of_trans_gt :
  ∀ {startPos : String.Pos} (pgt : PosGt startPos) (pge : PosGe pgt),
    pge.val.byteIdx ≥ startPos.byteIdx := by
  intro startPos pgt pge
  obtain ⟨pos, hgt⟩ := pgt
  obtain ⟨pos', hge⟩ := pge
  simp_all only [ge_iff_le]
  simp_all only [gt_iff_lt]
  omega

theorem PosGe.ge_of_next_of_ge_of_ge :
  ∀ (s : String) (startPos : String.Pos) (h : ¬s.atEnd startPos = true)
    (pos : PosGe (s.next' startPos h)) (endPos : PosGe pos.val),
    endPos.val.byteIdx ≥ startPos.byteIdx := by
  intro s startPos h pos endPos
  obtain ⟨pos, hpos⟩ := pos
  obtain ⟨endPos, hEndPos⟩ := endPos
  have := String.lt_next' s startPos
  have := String.next'_eq s startPos
  rw [this] at *
  simp_all only [ge_iff_le, String.pos_lt_eq, Bool.false_eq_true, not_false_eq_true,
    String.next'_eq, imp_self]
  simp_all only [ge_iff_le]
  omega

theorem PosGe.ge_of_trans_ge :
  ∀ {startPos : String.Pos} {pge : PosGe startPos} (pge' : PosGe pge.val),
    pge'.val.byteIdx ≥ startPos.byteIdx := by
  intro startPos pgt pge
  obtain ⟨pos, hgt⟩ := pgt
  obtain ⟨pos', hge⟩ := pge
  simp_all only [ge_iff_le]
  simp only [ge_iff_le] at hge
  omega

theorem PosGe.ge_of_ge :
  ∀ {startPos pos : String.Pos} (endPos : PosGe pos),
    pos.byteIdx ≥ startPos.byteIdx → endPos.val.byteIdx ≥ startPos.byteIdx := by
  intro startPos pos endPos
  obtain ⟨endPos, hendPos⟩ := endPos
  simp_all only [ge_iff_le]
  omega

theorem String.add_gt
  : ∀ (pos : String.Pos) (s : String),
    s.utf8ByteSize > 0 → (pos + s).byteIdx > pos.byteIdx := by
  intro pos s h
  simp_all only [Bool.not_eq_true, gt_iff_lt, String.Pos.byteIdx_addString, Nat.lt_add_right_iff_pos]

theorem String.add_ge
  : ∀ (pos : String.Pos) (s : String),
    (pos + s).byteIdx ≥ pos.byteIdx := by
  intro pos s
  simp_all only [Bool.not_eq_true, gt_iff_lt, String.Pos.byteIdx_addString, Nat.lt_add_right_iff_pos]
  omega

/--
Tries to solve theorems of the form `s.utf8ByteSize > n`.
-/
macro "simp_str_size" : tactic => `(tactic|(
  rw [←String.size_toUTF8]
  simp [String.toUTF8, String.utf8EncodeChar, ByteArray.size]
))

macro "simp_pos" : tactic => `(tactic|(
  try simp_all only [GE.ge, LE.le, LT.lt]
  try simp_all only [Nat.le_eq, Nat.le_refl]
))
