/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Init.Data.Int.Basic
import KLR.Core.Basic
import KLR.Util

def List.forall {α : Type _} (L : List α) (P : α → Prop) : Prop :=
  match L with
  | .nil => True
  | .cons l L => P l ∧ List.forall L P

def List.dot [Mul α] [Add α] [Zero α] (L1 L2 : List α) : α :=
  (List.zipWith (· * ·) L1 L2).sum

namespace KLR.Core

-- NTS: Err should be handled in the operational semantics
-- NTS: An allocation is always inbounds for a LocalStore, we must do the PhyStore check
-- only if accessing the physical memory

structure LocalStore (α : Type _) where
  elems : Nat × Nat → Option α

instance : Inhabited (LocalStore α) where default := ⟨ fun _ => .none ⟩

@[simp] def LocalStore.get (s : LocalStore α) (c : Nat × Nat) : Option α := s.elems c

@[simp] def LocalStore.set (s : LocalStore α) (c : Nat × Nat) (v : Option α) :=
  { s with elems c' := if c == c' then v else s.elems c }

structure PhyStore (α : Type _) extends LocalStore α where
  pmax : Nat
  fmax : Nat

@[simp] def PhyStore.inbounds (s : PhyStore α) (c : Nat × Nat) : Bool :=
  c.1 < s.pmax && c.2 < s.fmax

/-
A model of NeuronCore memory banks.
The `bounded` field represents any tensors stored with explicit addresses.
The `unbounded` field represents automatically allocated addresses.

The semantics will include different allocation modes.
This means that we can prove the following chain of equivalences:

(prog A w/ realistic allocation modes)
  ≈ (prog A w/ unbounded allocations)
  ≈ ...
  ≈ (prog B w/ unbounded allocations)
  ≈ (prog B w/ realistic allocation modes)

so that the difficult parts of the proof can be done using unbounded allocation,
and equivalences to programs involving realistic allocation modes need only be done
at the peripheries. -/

abbrev UnboundedBank (α : Type _) := Array (LocalStore α)
abbrev UnboundedBank.inbounds (d : UnboundedBank α) (i : Nat) : Bool := i < d.size
abbrev UnboundedBank.get (d : UnboundedBank α) (i : Nat) : LocalStore α := d[i]!
abbrev UnboundedBank.set (d : UnboundedBank α) (i : Nat) (v : LocalStore α → LocalStore α) :
    UnboundedBank α := d.mapIdx (fun i' s => if i' == i then v s else s)
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

abbrev NeuronMemory := ChipMemory UInt8
