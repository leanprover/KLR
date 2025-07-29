import KLR.TGR.AST
import TensorLib.Shape
import KLR.Util

structure UnionFind where
  arr : Array Nat

namespace UnionFind

end UnionFind

abbrev Symbol := Nat

inductive Ty where
  | Var (name : Symbol)
  | Shapes (shapes : List TensorLib.Shape)

def Ty.replaceTerm (term : Ty) (replace : Symbol) (new : Ty) : Ty :=
  sorry

structure DimensionPair where
  par : Ty
  free : Ty

structure Ctx where
  substitution : List (KLR.TGR.Var × TensorLib.Shape)
deriving Inhabited, Repr

abbrev Unify T := EStateM String Ctx T

def updateSubstitution (replace : Symbol) (new : Ty) : Unify Unit := do
  sorry


def constraintGen (f : KLR.TGR.Function) : List (Ty × Ty) := sorry

partial def solve (constraints : List (Ty × Ty)) : Unify Unit := do
  match constraints with
  | (left, right) :: t =>
    match (left, right) with
    | (Ty.Shapes s0, Ty.Shapes s1) =>
      if s0 == s1 then
        solve t
      else
        throw s!"Shape mismatch: {s0} != {s1}"
    | (Ty.Var replace, new) | (new, Ty.Var replace) =>
      let constraints := t.map fun (l, r) => (l.replaceTerm replace new, r.replaceTerm replace new)
      updateSubstitution replace new
      solve constraints
  | [] => pure ()

def infer (f : KLR.TGR.Function) : Unify Unit :=
  constraintGen f |> solve


def f := KLR.TGR.Function.mk
  "main"
  []
  []
  [
    .assign "a" (.arg 0) ⟨ .mk [10, 100, 8], .float32 ⟩,
    .assign "b" (.arg 1) ⟨ .mk [10, 200, 8], .float32 ⟩,
    .assign "t" (.batchMatmul "a" "b") ⟨ .mk [10, 100, 200], .float32 ⟩,
  ]
