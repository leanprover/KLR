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

namespace KLR.Core

/-- A LocalStore represents an unboudned 2D region of memory. -/
structure LocalStore (α : Type _) where
  elems : Nat × Nat → Option α

instance : Inhabited (LocalStore α) where default :=
  ⟨ fun _ => .none ⟩

@[simp] def LocalStore.get (s : LocalStore α) (c : Nat × Nat) : Option α := s.elems c

@[simp] def LocalStore.set (s : LocalStore α) (c : Nat × Nat) (v : Option α) :=
  { s with elems c' := if c == c' then v else s.elems c }

/-- A PhyStore represents an bounded 2D region of memory, encoeded as a LocalStore with
an additional inbounds predicate. -/
structure PhyStore (α : Type _) extends LocalStore α where
  pmax : Nat
  fmax : Nat

@[simp] def PhyStore.inbounds (s : PhyStore α) (c : Nat × Nat) : Bool :=
  c.1 < s.pmax && c.2 < s.fmax

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

abbrev UnboundedBank (α : Type _) := Array (LocalStore α)
abbrev UnboundedBank.inbounds (d : UnboundedBank α) (i : Nat) : Bool := i < d.size
abbrev UnboundedBank.get (d : UnboundedBank α) (i : Nat) : LocalStore α := d[i]!
abbrev UnboundedBank.set (d : UnboundedBank α) (i : Nat) (v : LocalStore α → LocalStore α) : UnboundedBank α :=
  d.mapIdx (fun i' s => if i' == i then v s else s)
abbrev UnboundedBank.push (d : UnboundedBank α) (l : LocalStore α) : UnboundedBank α :=
  Array.push d l

structure DualMemory (α : Type _) where
  bounded : PhyStore α
  unbounded : UnboundedBank α

inductive DualMemoryStoreIndex
| in_bounded
| in_unbounded (i : Nat)
  deriving Repr, BEq

def DualMemory.in_memory {α} (d : DualMemory α) : DualMemoryStoreIndex → Prop
| .in_bounded => True
| .in_unbounded i => i < d.unbounded.size

def DualMemory.get_store {α} (d : DualMemory α) (ix : DualMemoryStoreIndex) (_ : in_memory d ix) :
    LocalStore α :=
  match ix with | .in_bounded => d.bounded.toLocalStore | .in_unbounded i => d.unbounded[i]

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

structure ChipMemory (α : Type _) where
  sbuf : DualMemory α
  psum : DualMemory α
  hbm : UnboundedBank α

/-- The memory that can be stored in a UnboundedStore -/
inductive UCell (α DataT : Type _)
| Real (_ : α)
| Data (_ : DataT)

abbrev NeuronMemory (DataT : Type _) := ChipMemory (UCell UInt8 DataT)


structure ProdChipMemory (T : Type _) where
  left : KLR.Core.ChipMemory T
  right : KLR.Core.ChipMemory T

inductive ProdIndex
| left (_ : KLR.Core.DualMemoryStoreIndex)
| right (_ : KLR.Core.DualMemoryStoreIndex)

section iris
-- TODO: Stabilize Heap in Iris-Lean
instance {T : Type _} : AllocHeap (ProdChipMemory T) ProdIndex T where
  get := sorry
  set := sorry
  fresh := sorry
  get_set_eq := sorry
  get_set_ne := sorry
  empty := sorry
  hmap := sorry
  merge := sorry
  get_empty := sorry
  get_hmap := sorry
  get_merge := sorry
  notFull := sorry
  get_fresh := sorry


instance {T1 T2 : Type _} : HasHHMap (ProdChipMemory T1) (ProdChipMemory T2) ProdIndex T1 T2 where
  hhmap := sorry
  hhmap_get := sorry

end iris

-- def TProd (H : Type _ → Type _) (T : Type _) : Type _ := H T × H T
