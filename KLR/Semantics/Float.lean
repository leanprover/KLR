/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Init.Data.Int.Basic
import KLR.Core.Basic
import KLR.Util

/-
## Floating point typeclasses

The operational semantics, as well as the logic, are parameterized by a representation
of floating point numbers.
-/

/-- Abstract representation of a floating point number. This class includes only
those syntax classes necessary to express floating point calculations, extensions
of `FloatRep` are used to state that the floats have different properties. -/
class FloatRep (f : Type _) extends Add f, Inhabited f where

/- TODO: A floating point representation contains a well-behaved family of integers -/
/- TODO: Assoc, Comm, etc -/
/- TODO: Fields etc... can we axiomatize ℝ in a typeclass rather than import mathlib? -/

/-
## Floating point instances
-/

/-- Symbolic representation of floats
These floating point numbers are uninterpreted, so two SymbolicFloat calculations are
equal iff they are do the same operations in the same order.  -/
inductive SymbolicFloat where
| value : SymbolicFloat
| add : SymbolicFloat → SymbolicFloat → SymbolicFloat
  deriving BEq

instance : FloatRep SymbolicFloat where
  default := .value
  add := .add


/- Indexed families of floating point types, used to represent multiple floating point types within
the same program.
TODO: Could also add coercions if that's what the hw does
-/
inductive FloatFamily {I : Type _} (ty : I → Type _) where
| err : FloatFamily ty
| ftype : (i : I) → (v : ty i) → FloatFamily ty

class abbrev FloatFamilyIndex (I : Type _) := BEq I, LawfulBEq I

/-- Pointwise lifting of a binop to a function of FloatFamilies, error when applied to differently
tagged floating point types. -/
def lift_binop {I : Type _} {ty : I → Type _} [FloatFamilyIndex I]
    (op : {i : I} → ty i → ty i → ty i) :
    FloatFamily ty → FloatFamily ty → FloatFamily ty
  | .ftype i1 v1, .ftype i2 v2 =>
      dite (i2 == i1)
        (fun H => .ftype i1 (op v1 ((congrArg ty <| LawfulBEq.eq_of_beq H) ▸ v2)))
        (fun _ => .err)
  | _, _ => .err

instance (I : Type _) (ty : I → Type _) [FloatFamilyIndex I] [∀ {i : I}, FloatRep (ty i)] :
    FloatRep (FloatFamily ty) where
  default := .err
  add := lift_binop Add.add
