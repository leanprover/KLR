/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Init.Data.Int.Basic
import KLR.Semantics.Lib
import KLR.Core.Basic
import KLR.Util
import Iris.Instances.heProp

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
  a.free_offset + List.dot a.free_strides i

def AffineMap.is_trivial (a : AffineMap) : Prop :=
  a.free_offset = 0 ∧
  a.par_offset = 0 ∧
  a.par_stride = 1 ∧
  a.free_strides = a.free_strides.map (fun _ => 1)

namespace KLR.Core

/-- A LocalStore represents an unboudned 2D region of memory. -/
structure LocalStore (α : Type _) where
  elems : Nat × Nat → Option α

instance : Heap (LocalStore α) (Nat × Nat) α where
  get s c := s.elems c
  set s n v := { elems n' := if n = n' then v else s.elems n' }
  empty := { elems _ := none }
  hmap f s := { elems n := s.elems n |>.bind (f n) }
  merge op x y := { elems n := Option.merge op (x.elems n) (y.elems n) }
  get_set_eq := by simp_all
  get_set_ne := by simp_all
  get_empty  := by simp_all
  get_hmap   := by simp_all
  get_merge  := by simp_all

instance {α β} : HasHHMap (LocalStore α) (LocalStore β) (Nat × Nat) α β where
  hhmap f s := ⟨fun i => Store.get s i |>.bind (f i)⟩
  hhmap_get {t k} f := by simp [Store.get]

instance : Inhabited (LocalStore α) where default := ⟨ fun _ => .none ⟩

/-
structure PhyStoreSpec where
  pmax : Nat
  fmax : Nat

@[simp] def PhyStoreSpec.inbounds (s : PhyStoreSpec) (c : Nat × Nat) : Prop :=
  c.1 < s.pmax ∧ c.2 < s.fmax

structure PhyStoreIndex (s : PhyStoreSpec) where
  index : Nat × Nat
  wf : s.inbounds index
-/


/-
A model of NeuronCore memory banks.
- The `bounded` field represents any tensors stored with explicit addresses. These correspond to
  memory locations on the actual chip.
- The `unbounded` field represents automatically allocated addresses. They do not correspond to
  real memory locations.

The semantics will include different allocation modes.
This means that we can prove the following chain of equivalences:

(prog A w/ only bounded allocations)         -- → If the allocation technique is known, then...
  ≈ (prog A w/ unbounded allocations)        -- -> If DataT has an encoding, then...
  ≈ (prog A w/ unbounded & data allocations) -- (always)
  ≈ ...
  ≈ (prog B w/ unbounded & data allocations) -- -> If DataT has an encoding, then...
  ≈ (prog B w/ unbounded allocations)        -- → If the allocation technique is known, then...
  ≈ (prog B w/ only bounded allocations)

so that the difficult parts of the proof can be done using unbounded allocation,
and equivalences to programs involving realistic allocation modes need only be done
at the peripheries.
-/


structure TensorBank (α : Type _) where
  bank : Nat → Option (LocalStore α)
  next_fresh : Nat

/-- Well-formedness of a TensorBank. -/
@[simp] def TensorBank.wf (c : TensorBank α) : Prop :=
  ∀ n, c.next_fresh ≤ n → c.bank n = none

instance : UnboundedHeap (TensorBank α) Nat (LocalStore α) where
  get b n := b.bank n
  set b n v := { bank := fun n' => if n' = n then v else b.bank n', next_fresh := max b.next_fresh n+1 }
  empty := { bank := fun _ => none, next_fresh := 0 }
  hmap f b := { bank n := (b.bank n).bind (f n), next_fresh := b.next_fresh}
  merge op x y := { bank n := Option.merge op (x.bank n) (y.bank n), next_fresh := max x.next_fresh y.next_fresh}
  notFull := TensorBank.wf
  fresh {c} _ := c.next_fresh
  get_set_eq := by simp_all
  get_set_ne := by grind
  get_empty := by simp_all
  get_hmap := by simp_all
  get_merge := by simp_all
  get_fresh {c} H := H _ c.next_fresh.le_refl
  notFull_empty := by simp
  notFull_set_fresh {b v} H := by
    simp <;> intro n Hn
    split
    · omega
    · apply H
      omega

instance {α β} : HasHHMap (TensorBank α) (TensorBank β) Nat (LocalStore α) (LocalStore β) where
  hhmap f s := ⟨fun i => Store.get s i |>.bind (f i), s.next_fresh⟩
  hhmap_get {t k} f := by simp [Store.get]

/-- Updating the store preserves wf -/
theorem TensorBank.set_wf {c : TensorBank α} (Hwf : wf c) : wf (set c n v) := by
  simp_all [Store.set]
  intro n' Hn'
  split <;> rename_i h; omega
  apply Hwf
  omega

/-- Hmap over the store preserves wf -/
theorem TensorBank.hmap_wf {c : TensorBank α} (Hwf : wf c) : wf (hmap f c) := by
  simp_all [Heap.hmap]

/-- Merging stores preserves wf -/
theorem TensorBank.merge_wf {x y : TensorBank α} (Hwfx : wf x) (Hwfy : wf y) : wf (merge op x y) := by
  simp_all [Heap.merge]
  intro n Hn
  rw [Hwfx _ (by omega), Hwfy _ (by omega)]
  rfl

/-- Structure describing the physical characteristics of a chip's memory banks -/
structure ChipMemorySpec where
  psumPhysSpec : PhyStoreSpec
  sbufPhysSpec : PhyStoreSpec

structure ChipMemory (α : Type _) where
  psumPhysical  : LocalStore α
  psumUnbounded : TensorBank α
  sbufPhysical  : LocalStore α
  sbufUnbounded : TensorBank α
  hbmUnbounded  : TensorBank α

inductive ChipIndex
| psumPhysIndex
| psumUnboundedIndex (tensor : Nat)
| sbufPhysIndex
| sbufUnboundedIndex (tensor : Nat)
| hbmIndex (tensor : Nat)

@[simp] def ChipMemory.get_store (c : ChipMemory α) (i : ChipIndex) : Option (LocalStore α) :=
  match i with
  | .psumPhysIndex          => some c.psumPhysical
  | .psumUnboundedIndex t   => Store.get c.psumUnbounded t
  | .sbufPhysIndex          => some c.sbufPhysical
  | .sbufUnboundedIndex t   => Store.get c.sbufUnbounded t
  | .hbmIndex t             => Store.get c.hbmUnbounded t

@[simp] def ChipMemory.set_store (c : ChipMemory α) (i : ChipIndex) (v : Option (LocalStore α)) : ChipMemory α :=
  match i with
  | .psumPhysIndex          => { c with psumPhysical  := v.getD Heap.empty }
  | .psumUnboundedIndex t   => { c with psumUnbounded := Store.set c.psumUnbounded t v }
  | .sbufPhysIndex          => { c with sbufPhysical  := v.getD Heap.empty }
  | .sbufUnboundedIndex t   => { c with sbufUnbounded := Store.set c.sbufUnbounded t v }
  | .hbmIndex t             => { c with hbmUnbounded := Store.set c.hbmUnbounded t v }

@[simp] def ChipMemory.empty_store : ChipMemory α := ⟨Heap.empty, Heap.empty, Heap.empty, Heap.empty, Heap.empty⟩

@[simp] def ChipMemory.hmap_store (f : ChipIndex → LocalStore α → Option (LocalStore α)) (t : ChipMemory α) : ChipMemory α where
  psumPhysical  := f .psumPhysIndex t.psumPhysical |>.getD Heap.empty
  psumUnbounded := Heap.hmap (fun i s => f (.psumUnboundedIndex i) s) t.psumUnbounded
  sbufPhysical  := f .sbufPhysIndex t.sbufPhysical |>.getD Heap.empty
  sbufUnbounded := Heap.hmap (fun i s => f (.sbufUnboundedIndex i) s) t.sbufUnbounded
  hbmUnbounded  := Heap.hmap (fun i s => f (.hbmIndex i) s) t.hbmUnbounded

@[simp] def ChipMemory.merge_store (op : LocalStore α → LocalStore α → LocalStore α) (x y : ChipMemory α) : ChipMemory α where
  psumPhysical  := op x.psumPhysical y.psumPhysical
  psumUnbounded := Heap.merge op x.psumUnbounded y.psumUnbounded
  sbufPhysical  := op x.sbufPhysical y.sbufPhysical
  sbufUnbounded := Heap.merge op x.sbufUnbounded y.sbufUnbounded
  hbmUnbounded  := Heap.merge op x.hbmUnbounded y.hbmUnbounded

def ChipMemory.hhmap_store (f : ChipIndex → LocalStore α → Option (LocalStore β)) (s : ChipMemory α) : ChipMemory β :=
  ⟨ f .psumPhysIndex s.psumPhysical |>.getD Heap.empty,
    hhmap (f <| .psumUnboundedIndex ·) s.psumUnbounded,
    f .sbufPhysIndex s.sbufPhysical |>.getD Heap.empty,
    hhmap (f <| .sbufUnboundedIndex ·) s.sbufUnbounded,
    hhmap (f <| .hbmIndex ·) s.hbmUnbounded ⟩

structure ChipCellIndex where
  chip : ChipIndex
  cell : Nat × Nat

@[simp] def ChipMemory.get (c : ChipMemory α) (i : ChipCellIndex) : Option α :=
  ChipMemory.get_store c i.chip |>.bind (Store.get · i.cell)

@[simp] def ChipMemory.set (c : ChipMemory α) (i : ChipCellIndex) (v : Option α) : ChipMemory α :=
  let tgt := ChipMemory.get_store c i.chip |>.getD Heap.empty
  ChipMemory.set_store c i.chip (some <| Store.set tgt i.cell v)

@[simp] def ChipMemory.empty : ChipMemory α :=
  ⟨Heap.empty, Heap.empty, Heap.empty, Heap.empty, Heap.empty⟩

@[simp] def ChipMemory.hmap (f : ChipCellIndex → α → Option α) (t : ChipMemory α) : ChipMemory α :=
  ChipMemory.hmap_store (fun i s => some <| Heap.hmap (f ⟨i, ·⟩ ·) s) t

@[simp] def ChipMemory.merge (op : α → α → α) (x y : ChipMemory α) : ChipMemory α :=
  ChipMemory.merge_store (Heap.merge op) x y

@[simp] def ChipMemory.hhmap (f : ChipCellIndex → α → Option β) (s : ChipMemory α) : ChipMemory β :=
  ChipMemory.hhmap_store (fun i s' => some <| HasHHMap.hhmap (f ⟨i, ·⟩ ·) s') s

theorem ChipMemory.get_set_eq {t : ChipMemory α} {k k' : ChipCellIndex} {v} : k = k' → get (set t k v) k' = v := by
  intro H; rcases k' with ⟨chip, cell⟩
  cases chip <;> simp_all [get, set, Store.get_set_eq]

theorem ChipMemory.get_set_ne {t : ChipMemory α} {k k' : ChipCellIndex} {v} : k ≠ k' → get (set t k v) k' = get t k' := by
  intro H; rcases k with ⟨chip1, cell1⟩; rcases k' with ⟨chip2, cell2⟩
  cases chip1 <;> cases chip2 <;>
  simp only [get, set, get_store, set_store, Store.get_set_ne]
  · simp; rw [Store.get_set_ne]; grind
  · rename_i i j
    simp [Option.bind, Option.getD]
    rcases Classical.em (i = j) with (hij|hij) <;>
    cases h : Store.get t.psumUnbounded i <;>
    simp only []
    · simp [Store.get_set_eq hij]
      subst hij; simp [h]
      rcases Classical.em (cell1 = cell2) with (hc|hc) <;> simp_all [Store.get_set_ne, Heap.get_empty]
    · simp [Store.get_set_eq hij]
      subst hij; simp [h]
      rcases Classical.em (cell1 = cell2) with (hc|hc) <;> simp_all [Store.get_set_ne, Heap.get_empty]
    · simp [Store.get_set_ne hij]
    · simp [Store.get_set_ne hij]
  · simp; rw [Store.get_set_ne]; grind
  · rename_i i j
    simp [Option.bind, Option.getD]
    rcases Classical.em (i = j) with (hij|hij) <;>
    cases h : Store.get t.sbufUnbounded i <;>
    simp only []
    · simp [Store.get_set_eq hij]
      subst hij; simp [h]
      rcases Classical.em (cell1 = cell2) with (hc|hc) <;> simp_all [Store.get_set_ne, Heap.get_empty]
    · simp [Store.get_set_eq hij]
      subst hij; simp [h]
      rcases Classical.em (cell1 = cell2) with (hc|hc) <;> simp_all [Store.get_set_ne, Heap.get_empty]
    · simp [Store.get_set_ne hij]
    · simp [Store.get_set_ne hij]
  · rename_i i j
    simp [Option.bind, Option.getD]
    rcases Classical.em (i = j) with (hij|hij) <;>
    cases h : Store.get t.hbmUnbounded i <;>
    simp only []
    · simp [Store.get_set_eq hij]
      subst hij; simp [h]
      rcases Classical.em (cell1 = cell2) with (hc|hc) <;> simp_all [Store.get_set_ne, Heap.get_empty]
    · simp [Store.get_set_eq hij]
      subst hij; simp [h]
      rcases Classical.em (cell1 = cell2) with (hc|hc) <;> simp_all [Store.get_set_ne, Heap.get_empty]
    · simp [Store.get_set_ne hij]
    · simp [Store.get_set_ne hij]

theorem ChipMemory.get_empty : get (empty : ChipMemory α) k = none := by
  rcases k with ⟨chip, _⟩; rcases chip <;> simp [empty, Heap.get_empty]

theorem ChipMemory.get_hmap : get (hmap f t) k = (get t k).bind (f k) := by
  rcases k with ⟨chip, _⟩
  cases chip
  · simp [hmap, Heap.get_hmap]
  · rename_i i j
    simp [Heap.get_hmap]
    cases (Store.get t.psumUnbounded j) <;> simp [Store.get, Heap.hmap]
  · simp [hmap, Heap.get_hmap]
  · rename_i i j
    simp [Heap.get_hmap]
    cases (Store.get t.sbufUnbounded j) <;> simp [Store.get, Heap.hmap]
  · rename_i i j
    simp [Heap.get_hmap]
    cases (Store.get t.hbmUnbounded j) <;> simp [Store.get, Heap.hmap]

theorem ChipMemory.get_merge : get (merge op t1 t2) k = Option.merge op (get t1 k) (get t2 k) := by
  rcases k with ⟨chip, _⟩
  cases chip
  · simp [hmap, Heap.get_merge]
  · rename_i i
    simp [hmap, Heap.get_merge, Option.merge]
    cases _ : Store.get t1.psumUnbounded i <;>
    cases _ : Store.get t2.psumUnbounded i <;>
    simp_all [Heap.get_merge] <;>
    grind
  · simp [hmap, Heap.get_merge]
  · rename_i i
    simp [hmap, Heap.get_merge, Option.merge]
    cases _ : Store.get t1.sbufUnbounded i <;>
    cases _ : Store.get t2.sbufUnbounded i <;>
    simp_all [Heap.get_merge] <;>
    grind
  · rename_i i
    simp [hmap, Heap.get_merge, Option.merge]
    cases _ : Store.get t1.hbmUnbounded i <;>
    cases _ : Store.get t2.hbmUnbounded i <;>
    simp_all [Heap.get_merge] <;>
    grind

instance ChipMemoryHeapInst : Heap (ChipMemory α) ChipCellIndex α where
  get        := ChipMemory.get
  set        := ChipMemory.set
  empty      := ChipMemory.empty
  hmap       := ChipMemory.hmap
  merge      := ChipMemory.merge
  get_set_eq := ChipMemory.get_set_eq
  get_set_ne := ChipMemory.get_set_ne
  get_empty  := ChipMemory.get_empty
  get_hmap   := ChipMemory.get_hmap
  get_merge  := ChipMemory.get_merge

instance {α β} : HasHHMap (ChipMemory α) (ChipMemory β) ChipCellIndex α β where
  hhmap := ChipMemory.hhmap
  hhmap_get {t k} f := by
    rcases k with ⟨chip, cell⟩
    cases chip <;>
    simp_all [Store.get, hhmap, ChipMemory.hhmap_store, Option.bind] <;>
    grind

structure ProdStore (T : Type _) where
  left  : T
  right : T

inductive ProdIndex (K : Type _) where
| left  (k : K)
| right (k : K)

instance [Heap T K V] : Heap (ProdStore T) (ProdIndex K) V where
  get h k :=
    match k with
    | .left k => Store.get h.left k
    | .right k => Store.get h.right k
  set h k v :=
    match k with
    | .left k => { h with left := Store.set h.left k v }
    | .right k => { h with right := Store.set h.right k v }
  empty := ⟨ Heap.empty, Heap.empty ⟩
  hmap f h := ⟨ Heap.hmap (fun k v => f (.left k)  v) h.left, Heap.hmap (fun k v => f (.right k) v) h.right ⟩
  merge op x y := ⟨ Heap.merge op x.left y.left, Heap.merge op x.right y.right ⟩
  get_set_eq {t k k' v} H := by cases k' <;> cases k <;> simp_all [Store.get_set_eq]
  get_set_ne {t k k' v} H := by cases k' <;> cases k <;> simp_all [Store.get_set_ne]
  get_empty {k} := by cases k <;> simp_all [Heap.get_empty]
  get_hmap {f t k} := by cases k <;> simp_all [Heap.get_hmap]
  get_merge {op x y} k := by cases k <;> simp_all [Heap.get_merge]

instance [Heap T1 K V1] [Heap T2 K V2] [HasHHMap T1 T2 K V1 V2] :
    HasHHMap (ProdStore T1) (ProdStore T2) (ProdIndex K) V1 V2 where
  hhmap f h := ⟨ hhmap (fun i v => f (.left i) v) h.1,  hhmap (fun i v => f (.right i) v) h.2⟩
  hhmap_get {t k} f := by cases k <;> simp [hhmap_get, Store.get]

/-- The memory that can be stored in a UnboundedStore -/
inductive UCell (α DataT : Type _)
| Real (_ : α)
| Data (_ : DataT)

abbrev NeuronMemory (DataT : Type _) := ChipMemory (UCell UInt8 DataT)
abbrev NeuronIndex := ChipCellIndex

abbrev ProdNeuronMemory (DataT : Type _) := ProdStore (ChipMemory (UCell UInt8 DataT))
abbrev ProdNeuronIndex := ProdIndex ChipCellIndex
