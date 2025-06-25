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
scoped notation "⋆" => Kind.typ

/-- Primitive types in the NKI type system. -/
inductive Prim
  | none
  | bool
  | int
  | float
  | string
  | dtype (dt : Core.Dtype) : Prim

/-- Types indexed by context and kind. -/
inductive Typ
  /-- Type variable reference -/
  | var (idx : Nat) : Typ
  /-- Polymorphic universal quantification -/
  | pi (κ : Kind) (typ : Typ) : Typ
  /-- Primitive types -/
  | prim (p : Prim) : Typ
  /-- Tuple types -/
  | tuple (ts : List Typ) : Typ
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
infixr:50 " ⇒ " => Typ.func

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
  | pi {Φ : TypCtx} (κ ι : Kind) (α : Typ)
    : (Φ,, κ ⊢⋆ α : ι) → Φ ⊢⋆ .pi κ α : ι
  | prim {Φ : TypCtx} (p : Prim) : Φ ⊢⋆ .prim p:⋆
  | tuple {Φ : TypCtx} {κ : Kind} (αs : List Typ)
    : (∀ α ∈ αs, Φ ⊢⋆ α : κ) → Φ ⊢⋆ .tuple αs : κ
  | func {Φ : TypCtx} (dom ran : Typ) : Φ ⊢⋆ dom ⇒ ran : ⋆
  | dim {Φ : TypCtx} (n : Nat) : Φ ⊢⋆ .dim n : .dim
  | shape {Φ : TypCtx} (dims : List Typ)
    : (∀ dim ∈ dims, Φ ⊢⋆ dim : .dim) → Φ ⊢⋆ .shape dims : .shape
  | tensor {Φ : TypCtx} (shape : Typ) (dt : Core.Dtype)
    : (Φ ⊢⋆ shape : .shape) → Φ ⊢⋆ .tensor shape dt : ⋆
  | dimAdd {Φ : TypCtx} (x y : Typ)
    : (Φ ⊢⋆ x : .dim) → (Φ ⊢⋆ y : .dim) → Φ ⊢⋆ .dimAdd x y : .dim
  | shapeAppend {Φ : TypCtx} (s1 s2 : Typ)
    : (Φ ⊢⋆ s1 : .shape) → (Φ ⊢⋆ s2 : .shape) → Φ ⊢⋆ .shapeAppend s1 s2 : .shape
  | dimEq {Φ : TypCtx} (x y : Typ)
    : (Φ ⊢⋆ x : .dim) → (Φ ⊢⋆ y : .dim) → Φ ⊢⋆ .dimEq x y : .prop

@[app_unexpander Typ.HasKind]
def unexpandHasKind : Lean.PrettyPrinter.Unexpander
  | `($_HasKind $Φ $α $κ) => `($Φ ⊢⋆ $α : $κ)
  | _ => throw ()

set_option pp.proofs false
#check Typ.HasKind.var (Φ := [⋆]) (κ := ⋆) 0 (by aesop)

end KLR.NKI.Types

namespace KLR.NKI

/-!
# Type Checking for NKI Kernels
-/

structure Ctx where
  typs : Types.TypCtx
  vars : List (String × Types.Typ)
  retTyp : Option Types.Typ

/--
  Set the type of the variable with `name` to be `typ`
-/
def Ctx.updateVar (Γ : Ctx) (name : String) (typ : Types.Typ) : Ctx :=
  let vars := (name, typ) :: Γ.vars.filter (·.1 == name)
  {Γ with vars := vars}

macro:65 v:term " :ᵥ " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.Value.HasTyp) $v $α)

inductive Value.HasTyp : Value → Types.Typ → Prop
  | none : .none :ᵥ (.prim .none)
  | bool {value : Bool} : (.bool value) :ᵥ (.prim .bool)
  | int {value : Int} : (.int value) :ᵥ (.prim .int)
  | float {value : Float} : (.float value) :ᵥ (.prim .float)
  | string {value : String} : (.string value) :ᵥ (.prim .string)
  /--
    Ellipsis can have any type.
    TODO: Should `α` here be kind-checked?
  -/
  | ellipsis {α : Types.Typ} : .ellipsis :ᵥ α
  | tensor {shape : List Nat} {dtypeStr : String} {dtype : Core.Dtype}
    : Core.Dtype.fromString dtypeStr = dtype
      → (.tensor shape dtypeStr) :ᵥ (.tensor (.shape (shape.map .dim)) dtype)

@[app_unexpander Value.HasTyp]
def unexpandHasKind : Lean.PrettyPrinter.Unexpander
  | `($_HasKind $v $α) => `($v :ᵥ $α)
  | _ => throw ()
#check Value.HasTyp.none

/--
TODO: The numeric ops are too strict. They should all look similar to the `floor` case.
-/
inductive BinOp.HasTyp : BinOp → Types.Typ → Types.Typ → Types.Typ → Prop
  -- Logical operations
  | land : BinOp.HasTyp .land (.prim .bool) (.prim .bool) (.prim .bool)
  | lor : BinOp.HasTyp .lor (.prim .bool) (.prim .bool) (.prim .bool)
  -- Comparison operations
  | eq {α : Types.Typ} : BinOp.HasTyp .eq α α (.prim .bool)
  | ne {α : Types.Typ} : BinOp.HasTyp .ne α α (.prim .bool)
  | lt_int : BinOp.HasTyp .lt (.prim .int) (.prim .int) (.prim .bool)
  | lt_float : BinOp.HasTyp .lt (.prim .float) (.prim .float) (.prim .bool)
  | le_int : BinOp.HasTyp .le (.prim .int) (.prim .int) (.prim .bool)
  | le_float : BinOp.HasTyp .le (.prim .float) (.prim .float) (.prim .bool)
  | gt_int : BinOp.HasTyp .gt (.prim .int) (.prim .int) (.prim .bool)
  | gt_float : BinOp.HasTyp .gt (.prim .float) (.prim .float) (.prim .bool)
  | ge_int : BinOp.HasTyp .ge (.prim .int) (.prim .int) (.prim .bool)
  | ge_float : BinOp.HasTyp .ge (.prim .float) (.prim .float) (.prim .bool)
  -- Arithmetic operations: numeric × numeric → numeric
  | add_int : BinOp.HasTyp .add (.prim .int) (.prim .int) (.prim .int)
  | add_float : BinOp.HasTyp .add (.prim .float) (.prim .float) (.prim .float)
  | sub_int : BinOp.HasTyp .sub (.prim .int) (.prim .int) (.prim .int)
  | sub_float : BinOp.HasTyp .sub (.prim .float) (.prim .float) (.prim .float)
  | mul_int : BinOp.HasTyp .mul (.prim .int) (.prim .int) (.prim .int)
  | mul_float : BinOp.HasTyp .mul (.prim .float) (.prim .float) (.prim .float)
  | div_int : BinOp.HasTyp .div (.prim .int) (.prim .int) (.prim .int)
  | div_float : BinOp.HasTyp .div (.prim .float) (.prim .float) (.prim .float)
  | mod_int : BinOp.HasTyp .mod (.prim .int) (.prim .int) (.prim .int)
  | pow_int : BinOp.HasTyp .pow (.prim .int) (.prim .int) (.prim .int)
  | pow_float : BinOp.HasTyp .pow (.prim .float) (.prim .float) (.prim .float)
  | floor_int_int : BinOp.HasTyp .floor (.prim .int) (.prim .int) (.prim .int)
  | floor_float_int : BinOp.HasTyp .floor (.prim .float) (.prim .int) (.prim .float)
  | floor_int_float : BinOp.HasTyp .floor (.prim .int) (.prim .float) (.prim .float)
  | floor_float_float : BinOp.HasTyp .floor (.prim .float) (.prim .float) (.prim .float)
  -- Bitwise operations
  | lshift : BinOp.HasTyp .lshift (.prim .int) (.prim .int) (.prim .int)
  | rshift : BinOp.HasTyp .rshift (.prim .int) (.prim .int) (.prim .int)
  | or : BinOp.HasTyp .or (.prim .int) (.prim .int) (.prim .int)
  | xor : BinOp.HasTyp .xor (.prim .int) (.prim .int) (.prim .int)
  | and : BinOp.HasTyp .and (.prim .int) (.prim .int) (.prim .int)

macro:65 Γ:term " ⊢ " e:term " :ₑ " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.Expr.HasTyp) $Γ $e $α)
macro:65 Γ:term " ⊢ " e:term " :ₑ' " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.Expr'.HasTyp) $Γ $e $α)

mutual
inductive Expr.HasTyp (Γ : Ctx) : Expr → Types.Typ → Prop
  | mk {expr : Expr'} {pos : Pos} {α : Types.Typ}
    : (Γ ⊢ expr :ₑ' α) → Γ ⊢ {expr, pos} :ₑ α

inductive Expr'.HasTyp (Γ : Ctx) : Expr' → Types.Typ → Prop
  | value {α : Types.Typ} {value : Value}
    : (value :ᵥ α) → Γ ⊢ .value value :ₑ' α
  | var {α : Types.Typ} (name : String)
    : (Γ.typs ⊢⋆ α : .typ) → (name, α) ∈ Γ.vars → Γ ⊢ .var name :ₑ' α
  -- TODO: `proj`
  | tuple {elements : List Expr} {αs : List Types.Typ}
    : List.Forall₂ (fun e α => Γ ⊢ e :ₑ α) elements αs
      → Γ ⊢ .tuple elements :ₑ' .tuple αs
  -- TODO: `access`
  | binOp {op : BinOp} {left right : Expr} {α β γ : Types.Typ}
    : BinOp.HasTyp op α β γ
    → (Γ ⊢ left :ₑ α)
    → (Γ ⊢ right :ₑ β)
    → Γ ⊢ .binOp op left right :ₑ' γ
  | ifExp {test body orelse : Expr} {α : Types.Typ}
    : (Γ ⊢ test :ₑ .prim .bool)
    → (Γ ⊢ body :ₑ α)
    → (Γ ⊢ orelse :ₑ α)
    → (Γ ⊢ .ifExp test body orelse :ₑ' α)
  | call {f : Expr} {args : List Expr} {argTypes : List Types.Typ} {keywords : List Keyword} {ran : Types.Typ}
    : keywords = []  -- Only positional arguments are allowed
    → (Γ ⊢ f :ₑ .tuple argTypes ⇒ ran)
    → List.Forall₂ (fun arg argTyp => Γ ⊢ arg :ₑ argTyp) args argTypes
    → Γ ⊢ .call f args keywords :ₑ' ran
end

@[app_unexpander Expr.HasTyp]
def unexpandExprHasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $e $α) => `($Γ ⊢ $e :ₑ $α)
  | _ => throw ()

@[app_unexpander Expr'.HasTyp]
def unexpandExpr'HasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $e $α) => `($Γ ⊢ $e :ₑ' $α)
  | _ => throw ()

#check Expr.HasTyp ⟨[], [], none⟩ ⟨.value <| .bool true, ⟨0, 0⟩⟩ (.prim .bool)
#check Expr'.HasTyp ⟨[], [], none⟩ (.value <| .bool true) (.prim .bool)

macro:65 Γ:term " ⊢ " s:term " :ₛ " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.Stmt.HasTyp) $Γ $s $α)
macro:65 Γ:term " ⊢ " s:term " :ₛ' " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.Stmt'.HasTyp) $Γ $s $α)

/-
  Todo: Handle new variables introduced by `assign` when type checking `Stmt`s.
        It's probably easier to transform them into let bindings.
-/

mutual
inductive Stmt.HasTyp : Ctx → Stmt → Types.Typ → Prop
  | mk {Γ : Ctx} {α : Types.Typ} {stmt : Stmt'} {pos : Pos}
    : (Γ ⊢ stmt :ₛ' α) → Γ ⊢ {stmt, pos} :ₛ α

inductive Stmt'.HasTyp : Ctx → Stmt' → Types.Typ → Prop
  | expr {Γ : Ctx} {e : Expr} {α : Types.Typ} : (Γ ⊢ e :ₑ α) → Γ ⊢ .expr e :ₛ' α
  -- TODO `assert`
  | ret {Γ : Ctx} {e : Expr} {α : Types.Typ} : (Γ ⊢ e :ₑ α) → Γ ⊢ .ret e :ₛ' α
  | assign_new_untyped {Γ : Ctx} {x : String} {pos : Pos} {e : Expr} {α : Types.Typ}
    : (Γ ⊢ e :ₑ α)
      → Γ ⊢ .assign {expr := .var x, pos} none (some e) :ₛ' (.prim .none)
  -- TODO other `assign` cases
  -- Only access and variables are allowed on the LHS,
  -- Acess is like a binray op
  -- Variable is a let-binding
  | ifStm {Γ : Ctx} {e : Expr} {thn els: List Stmt} {thnTyps elsTyps : List Types.Typ}
    : (Γ ⊢ e :ₑ .prim .bool)
      → List.Forall₂ (fun thn thnTyp => Γ ⊢ thn :ₛ thnTyp) thn thnTyps
      → List.Forall₂ (fun els elsTyp => Γ ⊢ els :ₛ elsTyp) els elsTyps
      → Γ ⊢ .ifStm e thn els :ₛ' (.prim .none)
  -- TODO `forLoop`
  | breakLoop {Γ : Ctx} : Γ ⊢ .breakLoop :ₛ' (.prim .none)
  | continueLoop {Γ : Ctx} : Γ ⊢ .continueLoop :ₛ' (.prim .none)
end

@[app_unexpander Stmt.HasTyp]
def unexpandStmtHasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $s $α) => `($Γ ⊢ $s :ₛ $α)
  | _ => throw ()

@[app_unexpander Stmt'.HasTyp]
def unexpandStmt'HasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $s $α) => `($Γ ⊢ $s :ₛ' $α)
  | _ => throw ()

#check Stmt.HasTyp ⟨[], [], none⟩ ⟨.expr ⟨.value <| .bool true, ⟨0, 0⟩⟩, ⟨0, 0⟩⟩ (.prim .bool)
#check Stmt'.HasTyp ⟨[], [], none⟩ (.expr ⟨.value <| .bool true, ⟨0, 0⟩⟩) (.prim .bool)

-- /-- TODO: Handle assignments -/
-- inductive List.StmtsHasTyp : Ctx → List Stmt → Types.Typ → Prop
--   | singleton {Γ : Ctx} {stmt : Stmt} {α : Types.Typ}
--     : (Γ ⊢ stmt :ₛ α) → List.StmtsHasTyp Γ [stmt] α
--   | cons {Γ : Ctx} {hd : Stmt} {tl : List Stmt} {α β : Types.Typ}
--     : (Γ ⊢ hd :ₛ α) → (Γ ⊢ hd :ₛ β) → List.StmtsHasTyp Γ (hd :: tl) β

-- /-- TODO: Recursion? -/
-- inductive Fun.HasTyp : Ctx → Fun → Types.Typ → Prop
--   | mk {Γ : Ctx} {name : String} {file : String} {line : Nat} {body : List Stmt} {args : List Param}
--     : Fun.HasTyp Γ {name, file, line, body, args} α
