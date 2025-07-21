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

import KLR.NKI.Typed.Types

namespace KLR.NKI.Typed

/-!
# Statically-Typed NKI

Key differences from Python:
- All assignments are treated as let-bindings
- Lexical Scopes
- Currying is supported
- No use-before-defs or mutual recursions
-/

inductive Value {T : Kind → Type} : Typ T ⋆ → Type
  | none : Value (.prim .none)
  | bool (value : Bool) : Value (.prim .bool)
  | int (value : Int) : Value (.prim <| .numeric .int)
  | float (value : Float) : Value (.prim <| .numeric .float)
  | string (value : String) : Value (.prim .string)
  | tensor (value : TensorLib.Tensor)
    : Value (.tensor (.shape <| value.shape.val.map .size) (.dtype <| value.dtype))

inductive Builtin {T : Kind → Type} : (κ : Kind) → Typ T κ → Type
  -- logical
  | land : Builtin ⋆ (.prim .bool ⟶ .prim .bool ⟶ .prim .bool)
  | lor : Builtin ⋆ (.prim .bool ⟶ .prim .bool ⟶ .prim .bool)
  | eq : Builtin (⋆ ⟶⋆ ⋆) (.all λ α => .var α ⟶ .var α ⟶ .prim .bool)
  | ne : Builtin (⋆ ⟶⋆ ⋆) (.all λ α => .var α ⟶ .var α ⟶ .prim .bool)
  | lt {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim .bool)
  | le {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim .bool)
  | gt {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim .bool)
  | ge {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim .bool)
  -- arithmetic
  | add {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric (n1.max n2)))
  | sub {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric (n1.max n2)))
  | mul {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric (n1.max n2)))
  | div {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric .float))
  | mod {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric (n1.max n2)))
  | pow {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric (n1.max n2)))
  | floor {n1 n2 : Numeric}
    : Builtin ⋆ (.prim (.numeric n1) ⟶ .prim (.numeric n2) ⟶ .prim (.numeric (n1.max n2)))
  -- iterators
  | range : Builtin ⋆ (.prim (.numeric .int) ⟶ .iter (.prim (.numeric .int)))

abbrev KindTyp (T : Kind → Type) := Σ κ : Kind, Typ T κ

inductive Expr (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) : (κ : Kind) → Typ T κ → Type
  | var {κ : Kind} {α : Typ T κ} (var : V κ α) : Expr T V κ α
  | value {α : Typ T ⋆} (value : Value α) : Expr T V ⋆ α
  | builtin {κ : Kind} {α : Typ T κ} (op : Builtin κ α) : Expr T V κ α
  | ifExp {α : Typ T ⋆} (test : Expr T V ⋆ (.prim .bool)) (body orelse : Expr T V ⋆ α) : Expr T V ⋆ α
  | app {α β : Typ T ⋆} (f : Expr T V ⋆ (α ⟶ β)) (arg : Expr T V ⋆ α) : Expr T V ⋆ β
  | typApp {κ ι : Kind} {α : T κ → Typ T ι} {res : Typ T ι}
    (f : Expr T V (κ ⟶⋆ ι) (.all α)) (arg : Typ T κ) : (α[arg] ↦ res) → Expr T V ι res

/--
Statements maintain context to restrict which operations are well-formed and properly typed.

For example, `break` and `continue` can only be used within loop contexts,
and `return` statements must contain expressions that match the current expected return type of the function.
-/
structure StmtCtx (T : Kind → Type) where
  /-- Expected return type, `none` if not within a function context -/
  ret : Option (KindTyp T)
  /-- Whether we are within a loop context -/
  loop : Bool

mutual

inductive Def (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) : (κ : Kind) → Typ T κ → Type
  | stmts {κ : Kind} {α : Typ T κ}
    (body : Stmt T V κ α ⟨some ⟨κ, α⟩, false⟩)
    : Def T V κ α
  | recur {κ : Kind} {α : Typ T κ}
    (μ : V κ α → Stmt T V κ α ⟨some ⟨κ, α⟩, false⟩)
    : Def T V κ α

inductive Stmt (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) : (κ : Kind) → Typ T κ → StmtCtx T → Type
  | seq {κ ι : Kind} {α : Typ T κ} {β : Typ T ι} {ctx : StmtCtx T}
    : Stmt T V κ α ctx
      → Stmt T V ι β ctx
      → Stmt T V ι β ctx
  | expr {κ : Kind} {α : Typ T κ} {ctx : StmtCtx T}
    (e : Expr T V κ α)
    : Stmt T V ⋆ (.prim .none) ctx
  | abs {α β : Typ T ⋆} {γ : Option (KindTyp T)} {loop : Bool}
    (body : V ⋆ α → Stmt T V ⋆ β ⟨some ⟨⋆, β⟩, loop⟩)
    : Stmt T V ⋆ (α ⟶ β) ⟨γ, loop⟩
  | typAbs {κ ι : Kind} {γ : Option (KindTyp T)} {loop : Bool}
    (t : T κ → Typ T ι)
    (body : (arg : T κ) → Stmt T V ι (t arg) ⟨some ⟨ι, t arg⟩, loop⟩)
    : Stmt T V (κ ⟶⋆ ι) (.all t) ⟨γ, loop⟩
  | ret {κ : Kind} {α : Typ T κ} {loop : Bool}
    (e : Expr T V κ α)
    : Stmt T V κ α ⟨some ⟨κ, α⟩, loop⟩
  | letBind {κ : Kind} {α : Typ T κ} {β : Typ T ⋆} {ctx : StmtCtx T}
    (rhs : Expr T V κ α)
    (body : V κ α → Stmt T V ⋆ β ctx)
    : Stmt T V ⋆ β ctx
  | letDef {κ : Kind} {α : Typ T κ} {β : Typ T ⋆} {γ : Option (KindTyp T)} {loop : Bool}
    (dfn : Def T V κ α)
    (body : V κ α → Stmt T V ⋆ β ⟨γ, loop⟩)
    : Stmt T V ⋆ β ⟨γ, loop⟩
  /--
    If statements without else branches always have type `none`.
    This ensures that if statements appearing at the end of functions with
    non-none return types are ill-typed.

    This is an over-approximation when the condition is always true.
  -/
  | ifStm {κ : Kind} {α : Typ T κ} {ctx : StmtCtx T}
    (e : Expr T V ⋆ (.prim .bool))
    (thn : Stmt T V κ α ctx)
    : Stmt T V ⋆ (.prim .none) ctx
  /--
    If statements at non-terminal positions:
    the two branches can have different types, but the entire statement has type `none`
  -/
  | ifElsStm {κ ι : Kind} {α : Typ T κ} {β : Typ T ι} {ctx : StmtCtx T}
    (e : Expr T V ⋆ (.prim .bool))
    (thn : Stmt T V κ α ctx)
    (els : Stmt T V ι β ctx)
    : Stmt T V ⋆ (.prim .none) ctx
  /--
    If statements at terminal positions:
    both branches must have the same type.
  -/
  | ifElsStmRet {κ : Kind} {α : Typ T κ} {ctx : StmtCtx T}
    (e : Expr T V ⋆ (.prim .bool))
    (thn els : Stmt T V κ α ctx)
    : Stmt T V κ α ctx
  | forLoop {α β : Typ T ⋆} {γ : Option (KindTyp T)} {loop : Bool}
    (iter : Expr T V ⋆ (.iter α))
    (body : V ⋆ α → Stmt T V ⋆ β ⟨γ, true⟩)
    : Stmt T V ⋆ (.prim .none) ⟨γ, loop⟩
  | whileLoop {κ : Kind} {α : Typ T κ} {γ : Option (KindTyp T)} {loop : Bool}
    (cond : Expr T V ⋆ (.prim .bool))
    (body : Stmt T V κ α ⟨γ, true⟩)
    : Stmt T V ⋆ (.prim .none) ⟨γ, loop⟩
  | breakLoop {α : Option (KindTyp T)} : Stmt T V ⋆ (.prim .none) ⟨α, true⟩
  | continueLoop {α : Option (KindTyp T)} : Stmt T V ⋆ (.prim .none) ⟨α,true⟩

end

/--
Helper definition to ensure type annotation of a `Stmt`
-/
abbrev Stmt.typed {T : Kind → Type} {V : (κ : Kind) → Typ T κ → Type} {κ : Kind} {ctx : StmtCtx T}
  (t : Typ T κ) (s : Stmt T V κ t ctx) : Stmt T V κ t ctx :=
  s

inductive Kernel (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) {κ : Kind} (α : Typ T κ)
  | dfn : Def T V κ α → Kernel T V α
  /--
    Free variables in NKI statements. These reference prior Lean definitions of NKI functions.

    Note: We have a linking problem here.
    When compiling a `Kernel` containing `fvar`s, we need to access Lean meta information
    to find the command that defined it and link it to the current definition.
    We must ensure proper deduplication of definitions during linking.

    We may also try inlining everything during NKI definition elaboration, but this
    also presents deduplication challenges.
  -/
  | fvar {ι : Kind} (β : Typ T ι) (body : V ι β → Kernel T V α) : Kernel T V α
