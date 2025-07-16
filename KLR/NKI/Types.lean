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

import KLR.Core.Operators

/--
Type-level membership with notation `s ∋ a : Type` where `a : α` and `s : γ`.
Since `α` is an `outParam`, the container type `γ` determines the element type.

This differs from the standard library `Membership` class because our `mem` function
returns a `Type` instead of a `Prop`, making it suitable for dependent De Bruijn indexing.
-/
class Mem (α : outParam (Type u)) (γ : Type v) where
  /-- The membership relation `s ∋ α : Type*` where `a : α` and `s : γ`. -/
  mem : γ → α → Type (max u v)
infix:60 " ∋ " => Mem.mem

/--
Dependent list membership for De Bruijn indexing.
-/
inductive List.Member {α : Type u} : List α → α → Type u
  | head {a : α} {as : List α} : List.Member (a::as) a
  | tail {bs : List α} {a b : α} : List.Member bs b → List.Member (a::bs) b

instance instMemList {α} : Mem α (List α) where
  mem := List.Member

namespace KLR.NKI.Types

/-- The kinds of types in our type system. -/
inductive Kind
  /-- Dimension values (natural numbers) -/
  | dim
  /-- Tensor shapes (lists of dimensions) -/
  | shape
  /-- Regular types -/
  | type
  /--
  Type-level propositions for constraint solving.

  These represent assertions about types that users write in function preambles.
  The type checker runs a solver to verify their satisfiability, rather than
  requiring explicit proof construction like in traditional theorem provers.
  They act as type constraints for the solver to handle automatically.

  The goal here is to have users write python `assert`s and parse them
  into types by reflecting python expressions up to the NKI type level.
  -/
  | prop
scoped notation "⋆" => Kind.type

abbrev TypCtx := List Kind

/-- Context extension: `Φ,, κ ≡ κ :: Φ`. -/
scoped notation:70 Φ:70 ",, " κ:71 => @List.cons Kind κ Φ

/-- Primitive types in the NKI type system. -/
inductive Prim
  | none
  | bool
  | int
  | float
  | string
  /--
  Data type wrapper for tensor indexing.
  Currently not directly constructible in the AST.
  -/
  | dtype (dt : Core.Dtype) : Prim

mutual

/-- Types indexed by context and kind. -/
inductive Types : TypCtx → Kind → Type
  /-- Type variable reference -/
  | var {Φ : TypCtx} {κ : Kind} (mem : Φ ∋ κ) : Types Φ κ
  /-- Polymorphic universal quantification -/
  | pi {Φ : TypCtx} (κ : Kind) (typ : Types (Φ,, κ) ⋆) : Types Φ ⋆
  /-- Primitive types -/
  | prim {Φ : TypCtx} (p : Prim) : Types Φ ⋆
  /-- Tuple types -/
  | tuple {Φ : TypCtx} (ts : TList Φ ⋆) : Types Φ ⋆
  /-- Function types -/
  | func {Φ : TypCtx} (dom ran : Types Φ ⋆) : Types Φ ⋆
  /-- Dimension literals -/
  | dim {Φ : TypCtx} (n : Nat) : Types Φ .dim
  /-- Tensor shapes -/
  | shape {Φ : TypCtx} (dims : TList Φ .dim) : Types Φ .shape
  /-- Tensor types with shape and data type -/
  | tensor {Φ : TypCtx} (shape : Types Φ .shape) (dt : Core.Dtype) : Types Φ ⋆
  -- Dimension operations
  /-- Dimension addition -/
  | dimAdd {Φ : TypCtx} (x y : Types Φ .dim) : Types Φ .dim
  -- Shape operations
  /-- Shape concatenation -/
  | shapeAppend {Φ : TypCtx} (s1 s2 : Types Φ .shape) : Types Φ .shape
  -- Propositions
  /-- Dimension equality constraint -/
  | dimEq {Φ : TypCtx} (x y : Types Φ .dim) : Types Φ .prop

/-- Homogeneous lists of types with the same kind. -/
inductive TList : TypCtx → Kind → Type
  | nil {Φ κ} : TList Φ κ
  | cons {Φ κ} (hd : Types Φ κ) (tl : TList Φ κ) : TList Φ κ

end

/-!
# Type notation and syntax
-/

/-- `Φ ⊢⋆ κ` denotes a type of kind `κ` under type context `Φ`. -/
scoped infix:50 " ⊢⋆ " => Types

scoped infixr:55 " → " => Types.func

/-- Most recently bound variable (De Bruijn index 0) -/
scoped notation "v0" => Types.var List.Member.head
/-- Second most recently bound variable (De Bruijn index 1) -/
scoped notation "v1" => Types.var <| List.Member.tail List.Member.head
/-- Third most recently bound variable (De Bruijn index 2) -/
scoped notation "v2" => Types.var <| List.Member.tail <| List.Member.tail List.Member.head
/-- Fourth most recently bound variable (De Bruijn index 3) -/
scoped notation "v3" => Types.var <| List.Member.tail <| List.Member.tail <| List.Member.tail List.Member.head

/--
`Π κ, ι ⇒ body` binds kinds `κ` and `ι` in `body` using `Types.pi`.
Variables are accessible as `v0` (for `ι`), `v1` (for `κ`), etc.
-/
scoped macro "Π " κs:term,+ " ⇒ " body:term : term => do
  κs.getElems.foldrM (fun arg body => `(Types.pi $arg $body)) body

instance {Φ n} : OfNat (Types Φ .dim) n := ⟨.dim n⟩

instance {Φ} : Add (Types Φ .dim) where
  add := Types.dimAdd

instance {Φ} : Append (Types Φ .shape) where
  append := Types.shapeAppend

scoped infix:50 " == " => Types.dimEq

open Lean in
/--
List syntax for `TList`s. Each kind has a special prefix to avoid syntax conflicts.
-/
def expandTList (ts : TSyntaxArray `term) (ι : TSyntax `term) : MacroM (TSyntax `term) := do
  let nil : Lean.TSyntax `term ← `(TList.nil (κ := $ι))
  let l ← ts.foldrM (fun hd tl => do return ← `(TList.cons ($hd) <| $tl)) nil
  return l

/-- Dimension list syntax: `d[1, 2, 3]` -/
scoped macro "d[" ts:term,* "]" : term => do expandTList ts (← `(Kind.dim))
/-- Shape list syntax: `s[shape1, shape2]` -/
scoped macro "s[" ts:term,* "]" : term => do expandTList ts (← `(Kind.shape))
/-- Type list syntax: `⋆[type1, type2]` -/
scoped macro "⋆[" ts:term,* "]" : term => do expandTList ts (← `(Kind.type))

namespace TypesExamples

/--
Matrix multiplication.

Equivalent Python signature:
```python
def matmul(x, y):
  """
  Args:
    x: tensor of shape M x N
    y: tensor of shape N x K
  Return:
    out: tensor of shape M x K
  """
```
-/
def matMul {Φ} (dtype : Core.Dtype) : Φ ⊢⋆ ⋆ :=
  Π .dim, .dim, .dim ⇒
    let M := v2
    let N := v1
    let K := v0
    let x := .tensor (.shape d[M, N]) dtype
    let y := .tensor (.shape d[N, K]) dtype
    let out := .tensor (.shape d[M, K]) dtype
    .tuple ⋆[x, y] → out

/--
Batched matrix multiplication.

Equivalent Python signature:
```python
def batch_matmul(x, y):
  """
  Args:
    x: tensor of shape ... x M x N
    y: tensor of shape ... x N x K
  Return:
    out: tensor of shape ... x M x K
  """
```
-/
def batchMatMul {Φ} (dtype : Core.Dtype) : Φ ⊢⋆ ⋆ :=
  Π .dim, .dim, .dim, .shape ⇒
    let M := v3
    let N := v2
    let K := v1
    let batch := v0
    let x := .tensor (batch ++ (.shape d[M, N])) dtype
    let y := .tensor (batch ++ (.shape d[N, K])) dtype
    let out := .tensor (batch ++ (.shape d[M, K])) dtype
    .tuple ⋆[x, y] → out

/--
Concatenation along the last axis.

Equivalent Python signature:
```python
def concat_last_axis(x, y):
  """
  Args:
    x: tensor of shape ... x M
    y: tensor of shape ... x N
  Return:
    out: tensor of shape ... x (M + N)
  """
```
-/
def concatLastAxis {Φ} (dtype : Core.Dtype) : Φ ⊢⋆ ⋆ :=
  Π .dim, .dim, .shape ⇒
    let M := v2
    let N := v1
    let shape := v0
    let x := .tensor (shape ++ (.shape d[M])) dtype
    let y := .tensor (shape ++ (.shape d[N])) dtype
    let out := .tensor (shape ++ (.shape d[M + N])) dtype
    .tuple ⋆[x, y] → out

end TypesExamples

end KLR.NKI.Types
