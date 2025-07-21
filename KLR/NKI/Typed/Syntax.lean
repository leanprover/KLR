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
-/

inductive Value {T : Kind → Type} : Typ T ⋆ → Type
  | none : Value (.prim .none)
  | bool (value : Bool) : Value (.prim .bool)
  | int (value : Int) : Value (.prim .int)
  | float (value : Float) : Value (.prim .float)
  | string (value : String) : Value (.prim .string)
  | tensor (value : TensorLib.Tensor)
    : Value (.tensor (.shape <| value.shape.val.map .size) (.dtype <| value.dtype))

/--
TODO: Manage overloading better?
-/
inductive Builtin {T : Kind → Type} : (κ : Kind) → Typ T κ → Type
  -- logical
  | land : Builtin ⋆ (.prim .bool ⟶ .prim .bool ⟶ .prim .bool)
  | lor : Builtin ⋆ (.prim .bool ⟶ .prim .bool ⟶ .prim .bool)
  | eq : Builtin (⋆ ⟶⋆ ⋆) (.all λ α => .var α ⟶ .var α ⟶ .prim .bool)
  | ne : Builtin (⋆ ⟶⋆ ⋆) (.all λ α => .var α ⟶ .var α ⟶ .prim .bool)
  | lt_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | lt_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | lt_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | lt_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  | le_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | le_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | le_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | le_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  | gt_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | gt_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | gt_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | gt_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  | ge_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | ge_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | ge_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | ge_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  -- arithmetic
  | add_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | add_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | add_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | add_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | sub_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | sub_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | sub_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | sub_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | mul_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | mul_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | mul_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | mul_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | div_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | div_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | div_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | div_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | mod_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | mod_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | mod_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | mod_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | pow_int_int : Builtin ⋆ (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | pow_int_float : Builtin ⋆ (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | pow_float_int : Builtin ⋆ (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | pow_float_float : Builtin ⋆ (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | floor_int : Builtin ⋆ (.prim .int ⟶ .prim .int)
  | floor_float : Builtin ⋆ (.prim .float ⟶ .prim .int)

inductive Expr (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) : (κ : Kind) → Typ T κ → Type
  | var {κ : Kind} {α : Typ T κ} (var : V κ α) : Expr T V κ α
  | value {α : Typ T ⋆} (value : Value α) : Expr T V ⋆ α
  | builtin {κ : Kind} {α : Typ T κ} (op : Builtin κ α) : Expr T V κ α
  | ifExp {α : Typ T ⋆} (test : Expr T V ⋆ (.prim .bool)) (body orelse : Expr T V ⋆ α) : Expr T V ⋆ α
  | app {α β : Typ T ⋆} (f : Expr T V ⋆ (α ⟶ β)) (arg : Expr T V ⋆ α) : Expr T V ⋆ β
  | typApp {κ ι : Kind} {α : T κ → Typ T ι} {res : Typ T ι}
    (f : Expr T V (κ ⟶⋆ ι) (.all α)) (arg : Typ T κ) : (α[arg] ↦ res) → Expr T V ι res

abbrev KindTyp (T : Kind → Type) := Σ κ : Kind, Typ T κ

/--
Statements have a notion of context to restrict what kind of operations are well-formed/typed.

For example, `break` and `continue` can only be used in a loop context.
And `return` statements must contain expressions matching the current expected return type of the function.
-/
structure StmtCtx (T : Kind → Type) where
  /-- The current return type expected, `none` if not in a function context -/
  ret : Option (KindTyp T)
  /-- Whether we are in a loop context -/
  loop : Bool

inductive Stmt (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) : (κ : Kind) → Typ T κ → StmtCtx T → Type
  | expr {κ : Kind} {α : Typ T κ} {ctx : StmtCtx T}
    (e : Expr T V κ α)
    : Stmt T V κ α ctx
  | abs {α β : Typ T ⋆} {γ : Option (KindTyp T)} {loop : Bool}
    (body : V ⋆ α → Stmt T V ⋆ β ⟨some ⟨⋆, β⟩, loop⟩)
    : Stmt T V ⋆ (α ⟶ β) ⟨γ, loop⟩
  | typAbs {κ ι : Kind} {γ : Option (KindTyp T)} {loop : Bool}
    (t : T κ → Typ T ι)
    (body : (arg : T κ) → Stmt T V ι (t arg) ⟨some ⟨ι, t arg⟩, loop⟩)
    : Stmt T V (κ ⟶⋆ ι) (.all t) ⟨γ, loop⟩
  | rec_ {κ : Kind} {α : Typ T κ} {β : Option (KindTyp T)} {loop : Bool}
    (μ : V κ α → Stmt T V κ α ⟨some ⟨κ, α⟩, loop⟩)
    : Stmt T V κ α ⟨β, loop⟩
  | ret {κ : Kind} {α : Typ T κ} {loop : Bool}
    (e : Expr T V κ α)
    : Stmt T V κ α ⟨some ⟨κ, α⟩, loop⟩
  | let_ {κ : Kind} {α : Typ T κ} {β : Typ T ⋆} {ctx : StmtCtx T}
    (rhs : Expr T V κ α)
    (body : V κ α → Stmt T V ⋆ β ctx)
    : Stmt T V ⋆ β ctx
  | let_def {κ : Kind} {α : Typ T κ} {β : Typ T ⋆} {γ : Option (KindTyp T)} {loop : Bool}
    (rhs : Stmt T V κ α ⟨some ⟨κ, α⟩, loop⟩)
    (body : V κ α → Stmt T V ⋆ β ⟨γ, loop⟩)
    : Stmt T V ⋆ β ⟨γ, loop⟩
  /--
    An if statement without an else branch always has type none.
    This so that an if statement appearing at the end of a function with
    a non-none return type is ill-typed.

    This is an over-approximation when the condition is always true.
  -/
  | ifStm {κ : Kind} {α : Typ T κ} {ctx : StmtCtx T}
    (e : Expr T V ⋆ (.prim .bool))
    (thn : Stmt T V κ α ctx)
    : Stmt T V ⋆ (.prim .none) ctx
  | ifElsStm {κ : Kind} {α : Typ T κ} {ctx : StmtCtx T}
    (e : Expr T V ⋆ (.prim .bool))
    (thn els : Stmt T V κ α ctx)
    : Stmt T V κ α ctx
  | forLoop {α β : Typ T ⋆} {γ : Option (KindTyp T)} {loop : Bool}
    (x : V ⋆ α)
    (iter : Expr T V ⋆ (.iter α))
    (body : V ⋆ α → Stmt T V ⋆ β ⟨γ, true⟩)
    : Stmt T V ⋆ β ⟨γ, loop⟩
  | breakLoop {α : Option (KindTyp T)} : Stmt T V ⋆ (.prim .none) ⟨α, true⟩
  | continueLoop {α : Option (KindTyp T)} : Stmt T V ⋆ (.prim .none) ⟨α,true⟩
  | seq {κ ι : Kind} {α : Typ T κ} {β : Typ T ι} {ctx : StmtCtx T}
    (s1 : Stmt T V κ α ctx)
    (s2 : Stmt T V ι β ctx)
    : Stmt T V ι β ctx
  | def_ {κ : Kind} {α : Typ T κ} {β : Option (KindTyp T)} {loop : Bool}
    (f : Stmt T V κ α ⟨some ⟨κ, α⟩, loop⟩)
    : Stmt T V κ α ⟨β, loop⟩
  /--
  Free variables in a NKI statement. These are used to refer to prior Lean definitions of NKI functions.

  TODO: Move this out to a separate def.

  Note that we have a bit of a linking problem here:
  when compiling a `Stmt` containing `fvar`s, we need to go into Lean meta to find
  the command that defined it and link it to the current definition.
  We need to make sure to propery *dedup* definitions while linking.

  We may also try to just inline everything while elaborating a NKI def, but there's also dedup issues
  there as well.
  -/
  | fvar {κ ι : Kind} {β : Typ T ι} {γ : Option (KindTyp T)}
    (α : Typ T κ) (body : V κ α → Stmt T V ι β ⟨some ⟨ι, β⟩, false⟩)
    : Stmt T V ι β ⟨γ, false⟩

abbrev Stmt.typed {T : Kind → Type} {V : (κ : Kind) → Typ T κ → Type} {κ : Kind} {ctx : StmtCtx T}
  (t : Typ T κ) (s : Stmt T V κ t ctx) : Stmt T V κ t ctx :=
  s

abbrev Kernel (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) {κ : Kind} (t : Typ T κ)
  := Stmt T V κ t ⟨none, false⟩
