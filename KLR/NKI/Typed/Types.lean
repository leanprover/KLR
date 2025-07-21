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

import TensorLib.Tensor

namespace KLR.NKI.Typed

inductive Kind
  | size
  | shape
  | dtype
  | type
  | arrow (κ ι : Kind)
notation "⋆" => Kind.type
infixr:55 " ⟶⋆ " => Kind.arrow

inductive Numeric
  | int
  | float

abbrev Numeric.max : Numeric → Numeric → Numeric
  | .float, _ => .float
  | _, .float => .float
  | _, _ => .int

inductive Prim
  | none
  | bool
  | numeric (numeric : Numeric)
  | string
  | dtype (dt : TensorLib.Dtype)

inductive Typ (T : Kind → Type) : Kind → Type
  | var {κ : Kind} (var : T κ) : Typ T κ
  | all {κ ι : Kind} (typ : T κ → Typ T ι) : Typ T (κ ⟶⋆ ι)
  | prim (p : Prim) : Typ T ⋆
  | dtype (dtype : TensorLib.Dtype) : Typ T .dtype
  | arrow (α β : Typ T ⋆) : Typ T ⋆
  | size (n : Nat) : Typ T .size
  | shape (dims : List (Typ T .size)) : Typ T .shape
  | tensor (shape : Typ T .shape) (dt : Typ T .dtype) : Typ T ⋆
  | iter (e : Typ T ⋆) : Typ T ⋆
  | dimAdd (x y : Typ T .size) : Typ T .size
  | shapeAppend (s1 s2 : Typ T .shape) : Typ T .shape
infixr:55 " ⟶ " => Typ.arrow

/--
`t1[t2] ↦ t3` means substituting `t2` for the top-level bound variable in `t1` yields `t3`.
-/
macro:100 t1:term "[" t2:term "]" " ↦ " t3:term : term =>
  `($(Lean.mkIdent `Typ.Subst) $t1 $t2 $t3)

mutual

@[aesop safe constructors]
inductive Typ.SubstList {T : Kind → Type} : {κ ι : Kind} → List (T κ → Typ T ι) → Typ T κ → List (Typ T ι) → Prop
  | nil {t} : Typ.SubstList [] t []
  | cons {t1h t1t t t2h t2t}
    : (t1h[t] ↦ t2h) → Typ.SubstList t1t t t2t
      → Typ.SubstList (t1h :: t1t) t (t2h :: t2t)

/--
Relational type substitution rules
-/
@[aesop safe constructors]
inductive Typ.Subst {T : Kind → Type} : {κ ι : Kind} → (T κ → Typ T ι) → Typ T κ → Typ T ι → Prop
  | var_eq {t} : Typ.var[t] ↦ t -- Relies on η-reduction
  | var_ne {κ t} {v : T κ} : (fun _ => .var v)[t] ↦ (.var v)
  | abs {κ η ι} {t1 : T κ → T η → Typ T ι} {t1' : T η → Typ T ι} {t : Typ T κ} :
    (∀ v' : T η, (fun v => t1 v v')[t] ↦ (t1' v'))
    → (fun (v : T κ) => .all <| t1 v)[t] ↦ (.all t1')
  | prim {α t} : (fun _ => .prim α)[t] ↦ (.prim α)
  | dtype {dt t} : (fun _ => .dtype dt)[t] ↦ (.dtype dt)
  | arrow {t1 t1' t t2 t2'}
    : (t1[t] ↦ t1') → (t2[t] ↦ t2')
      → (fun v => t1 v ⟶ t2 v)[t] ↦ (t1' ⟶ t2')
  | size {n t} : (fun _ => .size n)[t] ↦ (.size n)
  | shape {sh t sh'}
    : (Typ.SubstList sh t sh')
      → (fun v => .shape <| (· v) <$> sh)[t] ↦ (.shape sh')
  | tensor {sh dt t sh' dt'}
    : (sh[t] ↦ sh') → (dt[t] ↦ dt') → (fun v => .tensor (sh v) (dt v))[t] ↦ .tensor sh' dt'
  | iter {e t e'}
    : (e[t] ↦ e') → (fun v => .iter (e v))[t] ↦ .iter e'
  | dimAdd {x y t x' y'}
    : (x[t] ↦ x') → (y[t] ↦ y') → (fun v => .dimAdd (x v) (y v))[t] ↦ (.dimAdd x' y')
  | shapeAppend {s1 s2 t s1' s2'}
    : (s1[t] ↦ s1') → (s2[t] ↦ s2') → (fun v => .shapeAppend (s1 v) (s2 v))[t] ↦ (.shapeAppend s1' s2')

end

@[app_unexpander Typ.Subst]
def unexpandTypSubst : Lean.PrettyPrinter.Unexpander
  | `($_subst $t1 $t2 $t3) => `(($t1)[$t2] ↦ $t3)
  | _ => throw ()

/--
Solve propositions of the form `t1[t2] ↦ t3`.

TODO: Implement specialized tactic with better error reporting than `aesop`
-/
macro "solve_subst" : tactic => `(tactic| aesop)
