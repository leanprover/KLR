/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Basic
import KLR.Core.Operators

namespace KLR.NKI.Types

/-!
# NKI's Type System
-/

inductive Kind
  | dim
  | shape
  | typ
  | prop
deriving DecidableEq
scoped notation "⋆" => Kind.typ

inductive Prim
  | none
  | bool
  | int
  | float
  | string
  | dtype (dt : Core.Dtype) : Prim

inductive Typ
  /-- Type variable reference -/
  | var (idx : Nat) : Typ
  /-- Polymorphic universal quantification -/
  | pi (κ : Kind) (typ : Typ) : Typ
  /-- Primitive types -/
  | prim (p : Prim) : Typ
  /-- Function types -/
  | func (dom ran : Typ) : Typ
  /-- Dimension literals -/
  | dim (n : Nat) : Typ
  /-- Tensor shapes -/
  | shape (dims : List Typ) : Typ
  /-- Tensor types with shape and data type -/
  | tensor (shape : Typ) (dt : Core.Dtype) : Typ
  -- Dimension operations
  /-- Dimension addition -/
  | dimAdd (x y : Typ) : Typ
  -- Shape operations
  /-- Shape concatenation -/
  | shapeAppend (s1 s2 : Typ) : Typ
  -- Propositions
  /-- Dimension equality constraint -/
  | dimEq (x y : Typ) : Typ
infixr:10 " ⟶ " => Typ.func

abbrev TypCtx := List Kind

/-- Context extension: `Φ,, κ ≡ κ :: Φ`. -/
scoped notation Φ:70 ",, " κ:71 => @List.cons Kind κ Φ

/-!
# Kind Checking for NKI Types
-/

macro:65 Φ:term:70 " ⊢⋆ " α:term " : " κ:term : term =>
  `($(Lean.mkIdent `KLR.NKI.Types.Typ.HasKind) $Φ $α $κ)

inductive Typ.HasKind : TypCtx → Typ → Kind → Prop
  | var {Φ : TypCtx} {κ : Kind}
    (i : Nat) (h : Φ[i]? = κ) : Φ ⊢⋆ .var i : κ
  | pi {Φ : TypCtx} {κ ι : Kind} {α : Typ}
    : (Φ,, κ ⊢⋆ α : ι) → Φ ⊢⋆ .pi κ α : ι
  | prim {Φ : TypCtx} {p : Prim} : Φ ⊢⋆ .prim p:⋆
  | func {Φ : TypCtx} {dom ran : Typ}
    : (Φ ⊢⋆ dom : ⋆) → (Φ ⊢⋆ ran : ⋆) → Φ ⊢⋆ dom ⟶ ran : ⋆
  | dim {Φ : TypCtx} {n : Nat} : Φ ⊢⋆ .dim n : .dim
  | shape {Φ : TypCtx} {dims : List Typ}
    : (∀ dim ∈ dims, Φ ⊢⋆ dim : .dim) → Φ ⊢⋆ .shape dims : .shape
  | tensor {Φ : TypCtx} {shape : Typ} {dt : Core.Dtype}
    : (Φ ⊢⋆ shape : .shape) → Φ ⊢⋆ .tensor shape dt : ⋆
  | dimAdd {Φ : TypCtx} {x y : Typ}
    : (Φ ⊢⋆ x : .dim) → (Φ ⊢⋆ y : .dim) → Φ ⊢⋆ .dimAdd x y : .dim
  | shapeAppend {Φ : TypCtx} {s1 s2 : Typ}
    : (Φ ⊢⋆ s1 : .shape) → (Φ ⊢⋆ s2 : .shape) → Φ ⊢⋆ .shapeAppend s1 s2 : .shape
  | dimEq {Φ : TypCtx} {x y : Typ}
    : (Φ ⊢⋆ x : .dim) → (Φ ⊢⋆ y : .dim) → Φ ⊢⋆ .dimEq x y : .prop

@[app_unexpander Typ.HasKind]
def unexpandHasKind : Lean.PrettyPrinter.Unexpander
  | `($_HasKind $Φ $α $κ) => `($Φ ⊢⋆ $α : $κ)
  | _ => throw ()

/--
`Π κ, ι ⇒ body` binds kinds `κ` and `ι` in `body` using `Types.pi`.
Variables are accessible as `Typ.var 0` (for `ι`), `Typ.var 1` (for `κ`), etc.
-/
scoped macro "Π " κs:term,+ " ⇒ " body:term : term => do
  κs.getElems.foldrM (fun arg body => `(Types.Typ.pi $arg $body)) body

instance {n} : OfNat (Types.Typ) n := ⟨.dim n⟩

instance : Add (Types.Typ) where
  add := Types.Typ.dimAdd

instance : Append (Types.Typ) where
  append := Types.Typ.shapeAppend

scoped infix:50 " == " => Types.Typ.dimEq

macro "dec_has_kind_cases" : tactic => `(tactic|(
  case isFalse => exact isFalse fun h => by cases h; contradiction
  case' isTrue =>
    rename_i $(Lean.mkIdent `h):ident
    try solve | (apply isTrue; constructor <;> try assumption)
))

macro "dec_has_kind_ih " Φ:term ", " α:term ", " κ:term : tactic => `(tactic|(
  cases $(Lean.mkIdent `Typ.decHasKind) $Φ $α $κ
  dec_has_kind_cases
))

macro "dec_has_kind_ih_list " Φ:term ", " αs:term ", " κ:term : tactic => `(tactic|(
  cases $(Lean.mkIdent `Typ.listDecHasKind) $Φ $αs $κ
  dec_has_kind_cases
))

macro "dec_has_kind_match_kind " κ:term ", " ι:term : tactic => `(tactic|(
  by_cases $(Lean.mkIdent `heq):ident : $κ = $ι
  case neg => exact isFalse fun h => by cases h; exact $(Lean.mkIdent `heq) rfl
  case' pos =>
    subst $(Lean.mkIdent `heq)
    try solve | (apply isTrue; constructor <;> try assumption)
))

mutual

instance Typ.listDecHasKind (Φ : TypCtx) (typs : List Typ) (κ : Kind) : Decidable (∀ α ∈ typs, Φ ⊢⋆ α : κ) :=
  match typs with
  | [] => isTrue fun _ h_mem => (List.not_mem_nil h_mem).elim
  | hd :: tl =>
    match Typ.decHasKind Φ hd κ with
    | isTrue h =>
      match Typ.listDecHasKind Φ tl κ with
      | isTrue h => isTrue fun _ h_mem => by
        simp_all only [List.mem_cons]
        cases h_mem with
        | inl h_2 =>
          subst h_2
          simp_all only
        | inr h_3 => simp_all only
      | isFalse hf => isFalse fun hf => by
        simp_all only [List.mem_cons, true_or, or_true, implies_true, not_true_eq_false]
    | isFalse hf =>
      isFalse fun h =>
        hf <| h hd (by
          simp_all only [List.mem_cons, true_or, not_true_eq_false]
        )

instance Typ.decHasKind (Φ : TypCtx) (α : Typ) (κ : Kind) : Decidable (Φ ⊢⋆ α : κ) := by
  match α with
  | var i =>
    match hm : Φ[i]? with
    | some ι =>
      if heq : κ = ι then
        exact isTrue (.var i <| heq ▸ hm)
      else
        apply isFalse
        intro h; cases h
        simp_all only [Option.some.injEq]
    | none =>
      apply isFalse
      intro h; cases h
      simp_all only [reduceCtorEq]
  | Π ι ⇒ β => dec_has_kind_ih (Φ,, ι), β, κ
  | prim p => dec_has_kind_match_kind κ, ⋆
  | func dom ran =>
    dec_has_kind_ih Φ, dom, ⋆
    dec_has_kind_ih Φ, ran, ⋆
    dec_has_kind_match_kind κ, ⋆
  | dim _ => dec_has_kind_match_kind κ, .dim
  | shape dims =>
    dec_has_kind_match_kind κ, .shape
    case pos => dec_has_kind_ih_list Φ, dims, .dim
  | tensor s dt =>
    dec_has_kind_match_kind κ, ⋆
    case pos => dec_has_kind_ih Φ, s, .shape
  | dimAdd x y =>
    dec_has_kind_match_kind κ, .dim
    case pos =>
      dec_has_kind_ih Φ, x, .dim
      dec_has_kind_ih Φ, y, .dim
  | shapeAppend s1 s2 =>
    dec_has_kind_match_kind κ, .shape
    case pos =>
      dec_has_kind_ih Φ, s1, .shape
      dec_has_kind_ih Φ, s2, .shape
  | dimEq x y =>
    dec_has_kind_match_kind κ, .prop
    case pos =>
      dec_has_kind_ih Φ, x, .dim
      dec_has_kind_ih Φ, y, .dim

end

namespace TypesExamples
open Typ

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
def matMul (dtype : Core.Dtype) : Typ :=
  Π .dim, .dim, .dim ⇒
    let M := var 2
    let N := var 1
    let K := var 0
    let x := tensor (shape [M, N]) dtype
    let y := tensor (shape [N, K]) dtype
    let out := tensor (shape [M, K]) dtype
    x ⟶ y ⟶ out

example {Φ dtype} : Φ ⊢⋆ matMul dtype : ⋆ := by
  apply of_decide_eq_true
  rfl

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
def batchMatMul (dtype : Core.Dtype) : Typ :=
  Π .dim, .dim, .dim, .shape ⇒
    let M := var 3
    let N := var 2
    let K := var 1
    let batch := var 0
    let x := tensor (batch ++ (shape [M, N])) dtype
    let y := tensor (batch ++ (shape [N, K])) dtype
    let out := tensor (batch ++ (shape [M, K])) dtype
    x ⟶ y ⟶ out

example {Φ dtype} : Φ ⊢⋆ batchMatMul dtype : ⋆ := by
  apply of_decide_eq_true
  rfl

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
def concatLastAxis (dtype : Core.Dtype) : Typ :=
  Π .dim, .dim, .shape ⇒
    let M := var 2
    let N := var 1
    let s := var 0
    let x := tensor (s ++ (shape [M])) dtype
    let y := tensor (s ++ (shape [N])) dtype
    let out := tensor (s ++ (shape [M + N])) dtype
    x ⟶ y ⟶ out

example {Φ dtype} : Φ ⊢⋆ concatLastAxis dtype : ⋆ := by
  apply of_decide_eq_true
  rfl
