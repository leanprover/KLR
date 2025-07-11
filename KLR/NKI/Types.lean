/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Basic
import KLR.Core.Operators
import KLR.Compile.Pass

namespace KLR.NKI.Types

/-!
# NKI's Type System

Tensor terminology:
- Dimension: The number of axes/directions along which data is arranged.
- Rank: The number dimensions in a tensor.
- Size: The number of things in a dimension.
- Shape: A list of sizes, one for each dimension in a tensor.

Examples:

The vector
[1, 2, 3, 4, 5]:
- has 1 dimension
- is of rank 1
- has size 5 in the 1st dimension
- has shape [5]

The matrix
[
  [1, 2],
  [3, 4],
  [5, 6],
]:
- has 2 dimensions
- is of rank 2
- has size 3 in the 1st dimension, 2 in the 2nd dimension
- has shape [3, 2]
-/

inductive Kind
  | size
  | shape
  | typ
deriving DecidableEq, BEq, Repr

inductive Prim
  | none
  | bool
  | int
  | float
  | string
  | dtype (dt : Core.Dtype)
deriving DecidableEq, BEq

inductive Typ
  /-- Type variable reference -/
  | var (idx : Nat)
  /-- Polymorphic universal quantification -/
  | pi (κ : Kind) (typ : Typ)
  /-- Primitive types -/
  | prim (p : Prim)
  /-- Function types -/
  | func (dom ran : Typ)
  /-- Size literals -/
  | size (n : Nat)
  /-- Tensor shapes -/
  | shape (sizes : List Typ)
  /-- Tensor types with shape and data type -/
  | tensor (shape : Typ) (dt : Core.Dtype)
  -- Dimension operations
  /-- Size addition -/
  | sizeAdd (x y : Typ)
  -- Shape operations
  /-- Shape concatenation -/
  | shapeAppend (s1 s2 : Typ)
  /-- The tail of a shape -/
  | shapeTail (s : Typ)
deriving BEq

def Kind.toString : Kind → String
  | .size => "size"
  | .shape => "shape"
  | .typ => "⋆"

instance Kind.instToStringKind : ToString Kind where
  toString := Kind.toString

instance Kind.instReprKind : Repr Kind where
  reprPrec k _ := k.toString

def Prim.toString : Prim → String
  | .none => "none"
  | .bool => "bool"
  | .int => "int"
  | .float => "float"
  | .string => "string"
  | .dtype dt => dt.toString

instance Prim.instToStringPrim : ToString Prim where
  toString := Prim.toString

instance Prim.instReprPrim : Repr Prim where
  reprPrec p _ := p.toString

def Typ.reprPrec (t : Typ) (n : Nat) : Std.Format :=
  match t with
  | .var idx => s!"v_{idx}"
  | .pi κ typ => s!"Π {κ} ⇒ {typ.reprPrec 1000}"
  | .prim p => p.toString
  | .func dom ran =>
    let fmt := s!"{dom.reprPrec n} ⟶ {ran.reprPrec (n + 1)}"
    if n > 10 then
      fmt
    else
      Std.Format.paren fmt
  | .size n => s!"size({n})"
  | .shape dims =>
    let dims := Std.Format.join (dims.map fun t => (Typ.reprPrec t 1000) ++ ", ")
    s!"shape[{dims}]"
  | .tensor sh dt =>
    s!"tensor[{sh.reprPrec 1000}, {dt}]"
  | .sizeAdd x y =>
    let fmt := s!"{x.reprPrec (n + 1)} + {y.reprPrec n}"
    if n > 50 then
      fmt
    else
      Std.Format.paren fmt
  | .shapeAppend s1 s2 =>
    let fmt := s!"{s1.reprPrec (n + 1)} ++ {s2.reprPrec n}"
    if n > 50 then
      fmt
    else
      Std.Format.paren fmt
  | .shapeTail t =>
    s!"({t.reprPrec 1000}).tail"

instance Typ.instReprTyp : Repr Typ where
  reprPrec :=  Typ.reprPrec

/-!
# Some syntax for writing down types
-/

scoped notation "⋆" => Kind.typ

infixr:10 " ⟶ " => Typ.func

/--
`Π κ, ι ⇒ body` binds kinds `κ` and `ι` in `body` using `Types.pi`.
Variables are accessible as `Typ.var 0` (for `ι`), `Typ.var 1` (for `κ`), etc.
-/
scoped macro "Π " κs:term,+ " ⇒ " body:term : term => do
  κs.getElems.foldrM (fun arg body => `(Types.Typ.pi $arg $body)) body

instance {n} : OfNat (Types.Typ) n := ⟨.size n⟩

instance : Add (Types.Typ) where
  add := Types.Typ.sizeAdd

instance : Append (Types.Typ) where
  append := Types.Typ.shapeAppend

scoped infix:50 " == " => Types.Typ.dimEq

/-!
# Variable substitution in types
-/

/--
`t[i := x]` substitutes `x` for the type variable with index `i` in `t`.
-/
macro:100 t:term "[" i:term " := " x:term "]" : term =>
  `($(Lean.mkIdent `KLR.NKI.Types.Typ.subst) $x $i $t)

/--
`x.subst i t` substitutes `x` for the type variable with index `i` in `t`.

We use the syntax `t[i := x] ≡ Typ.subst x i t`
-/
def Typ.subst (x : Typ) (i : Nat) : Typ → Typ
  | var j => if i == j then x else var j
  | pi κ typ => pi κ (typ[i + 1 := x])
  | prim p => prim p
  | func dom ran => func (dom[i := x]) (ran[i := x])
  | size n => size n
  | shape dims => shape (dims.map (·[i := x]))
  | tensor sh dt => tensor (sh[i := x]) dt
  | sizeAdd d1 d2 => sizeAdd (d1[i := x]) (d2[i := x])
  | shapeAppend s1 s2 => shapeAppend (s1[i := x]) (s2[i := x])
  | shapeTail s => shapeTail (s[i := x])

@[app_unexpander Typ.subst]
def unexpandTypSubst : Lean.PrettyPrinter.Unexpander
  | `($_subst $x $i $t) => `(($t)[$i := $x])
  | _ => throw ()
-- #check Typ.subst (.prim .int) 0 (.var 0 ⟶ Π .typ ⇒ .var 0)
-- #eval Typ.subst (.prim .int) 0 (.var 0 ⟶ Π .typ ⇒ .var 0)

-- TODO: This notion of equivalence is too strong.
-- We need to reason about equivalence of shapes constructed with operators, subtyping,
-- and maybe α-equivalence
def Typ.compat (t1 t2 : Typ) : Prop :=
  t1 == t2

instance Typ.instHasEquivTyp : HasEquiv Typ where
  Equiv := Typ.compat

instance Typ.decEquiv {t1 t2 : Typ} : Decidable (t1 ≈ t2) := by
  simp only [HasEquiv.Equiv, compat]
  cases t1 == t2
  · apply isFalse; simp only [Bool.false_eq_true, not_false_eq_true]
  · exact isTrue rfl

/-!
# Kind Checking for NKI Types
-/

abbrev TypCtx := List Kind

/-- Context extension: `Φ,, κ ≡ κ :: Φ`. -/
scoped notation Φ:70 ",, " κ:71 => @List.cons Kind κ Φ

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
  | size {Φ : TypCtx} {n : Nat} : Φ ⊢⋆ .size n : .size
  | shape {Φ : TypCtx} {sizes : List Typ}
    : (∀ size ∈ sizes, Φ ⊢⋆ size : .size) → Φ ⊢⋆ .shape sizes : .shape
  | tensor {Φ : TypCtx} {shape : Typ} {dt : Core.Dtype}
    : (Φ ⊢⋆ shape : .shape) → Φ ⊢⋆ .tensor shape dt : ⋆
  | sizeAdd {Φ : TypCtx} {x y : Typ}
    : (Φ ⊢⋆ x : .size) → (Φ ⊢⋆ y : .size) → Φ ⊢⋆ .sizeAdd x y : .size
  | shapeAppend {Φ : TypCtx} {s1 s2 : Typ}
    : (Φ ⊢⋆ s1 : .shape) → (Φ ⊢⋆ s2 : .shape) → Φ ⊢⋆ .shapeAppend s1 s2 : .shape
  | shapeTail {Φ : TypCtx} {s : Typ}
    : (Φ ⊢⋆ s : .shape) → Φ ⊢⋆ .shapeTail s : .shape

@[app_unexpander Typ.HasKind]
def unexpandHasKind : Lean.PrettyPrinter.Unexpander
  | `($_HasKind $Φ $α $κ) => `($Φ ⊢⋆ $α : $κ)
  | _ => throw ()

/-!
# Tactics for proving the decidability of kind-checking
-/

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

/--
Prove kind-checking of types is decidable
-/
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
    dec_has_kind_match_kind κ, ⋆
    case pos =>
      dec_has_kind_ih Φ, dom, ⋆
      dec_has_kind_ih Φ, ran, ⋆
  | size _ => dec_has_kind_match_kind κ, .size
  | shape sizes =>
    dec_has_kind_match_kind κ, .shape
    case pos =>
      dec_has_kind_ih_list Φ, sizes, .size
  | tensor s dt =>
    dec_has_kind_match_kind κ, ⋆
    case pos =>
      dec_has_kind_ih Φ, s, .shape
  | sizeAdd x y =>
    dec_has_kind_match_kind κ, .size
    case pos =>
      dec_has_kind_ih Φ, x, .size
      dec_has_kind_ih Φ, y, .size
  | shapeAppend s1 s2 =>
    dec_has_kind_match_kind κ, .shape
    case pos =>
      dec_has_kind_ih Φ, s1, .shape
      dec_has_kind_ih Φ, s2, .shape
  | shapeTail s =>
    dec_has_kind_match_kind κ, .shape
    case pos =>
      dec_has_kind_ih Φ, s, .shape

end

abbrev TypCheck := Compile.Pass.PosM Typ

def Typ.reduceShape (Φ : TypCtx) : Typ → TypCheck
  | .shape sizes =>
    if ∀ s ∈ sizes, Φ ⊢⋆ s : .size then
      return .shape sizes
    else
      throw "tensor dimension must have kind dim"
  | .shapeAppend s1 s2 => do
    let s1 ← s1.reduceShape Φ
    let s2 ← s2.reduceShape Φ
    match s1, s2 with
    | .shape dims1, .shape dims2 => return .shape (dims1 ++ dims2)
    | s1, s2 => return .shapeAppend s1 s2
  | .shapeTail s => do
    let s ← s.reduceShape Φ
    match s with
    | .shape [] => throw "cannot take the tail of an empty list of dimensions"
    | .shape (_::tl) => return .shape tl
    | s => return .shapeTail s
  | s =>
    if Φ ⊢⋆ s : .shape then
      return s
    else
      throw "expected kind shape"

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
  Π .size, .size, .size ⇒
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
  Π .size, .size, .size, .shape ⇒
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
  Π .size, .size, .shape ⇒
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
