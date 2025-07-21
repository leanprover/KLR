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
  | builtin {κ : Kind} {α : Typ T κ} (const : Builtin κ α) : Expr T V κ α
  | ifExp {α : Typ T ⋆} (test : Expr T V ⋆ (.prim .bool)) (body orelse : Expr T V ⋆ α) : Expr T V ⋆ α
  | app {α β : Typ T ⋆} (f : Expr T V ⋆ (α ⟶ β)) (arg : Expr T V ⋆ α) : Expr T V ⋆ β
  | typApp {κ ι : Kind} {α : T κ → Typ T ι} {res : Typ T ι}
    (f : Expr T V (κ ⟶⋆ ι) (.all α)) (arg : Typ T κ) : (α[arg] ↦ res) → Expr T V ι res

structure StmtCtx (T : Kind → Type) where
  /-- The current return type expected, `none` if not in a function context -/
  ret : Option (Typ T ⋆)
  /-- Whether we are in a loop context -/
  loop : Bool

inductive Stmt (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) : (κ : Kind) → Typ T κ → StmtCtx T → Type
  | expr {κ α ctx} (e : Expr T V κ α) : Stmt T V κ α ctx
  -- Is this really needed
  | nullaryAbs {α} (body : Stmt T V ⋆ α ⟨some α, false⟩) : Stmt T V ⋆ α ⟨none, false⟩
  | abs {α β ret} (body : V ⋆ α → Stmt T V ⋆ β ⟨some β, false⟩) : Stmt T V ⋆ (α ⟶ β) ⟨ret, false⟩
  | typAbs {κ ι : Kind}
    (t : T κ → Typ T ι)
    (body : (arg : T κ) → Stmt T V ι (t arg) ⟨none, false⟩)
    : Stmt T V (κ ⟶⋆ ι) (.all t) ⟨none, false⟩
  | ret {α loop} (e : Expr T V ⋆ α) : Stmt T V ⋆ α ⟨some α, loop⟩
  | let_ {κ β ctx} {α : Typ T κ} (rhs : Expr T V κ α)
    (body : V κ α → Stmt T V ⋆ β ctx) : Stmt T V ⋆ β ctx
  -- Do we need this case?
  | def_ {κ α ι β} (f : Stmt T V κ α ⟨none, false⟩) : Stmt T V ι β ⟨none, false⟩
  | def_cont {κ α ι β} (f : Stmt T V κ α ⟨none, false⟩) (c : V κ α → Stmt T V ι β ⟨none, false⟩)
    : Stmt T V ι β ⟨none, false⟩
  | rec_ {κ ctx} {α : Typ T κ} (rhs : V κ α → Stmt T V κ α ⟨none, false⟩) : Stmt T V κ α ctx
  -- Duplicate if-then-else to avoid needing to redefine Option inside a mutual block
  | ifStm {α ctx} (e : Expr T V ⋆ (.prim .bool)) (thn : Stmt T V ⋆ α ctx) : Stmt T V ⋆ α ctx
  | ifElsStm {α ctx} (e : Expr T V ⋆ (.prim .bool)) (thn els : Stmt T V ⋆ α ctx) : Stmt T V ⋆ α ctx
  | forLoop {α β ret loop} (x : V ⋆ α) (iter : Expr T V ⋆ (.iter α))
    (body : V ⋆ α → Stmt T V ⋆ β ⟨ret, true⟩) : Stmt T V ⋆ β ⟨ret, loop⟩
  | breakLoop {ret} : Stmt T V ⋆ (.prim .none) ⟨ret, true⟩
  | continueLoop {ret} : Stmt T V ⋆ (.prim .none) ⟨ret, true⟩
  | seq {α β ctx} (s1 : Stmt T V ⋆ α ctx) (s2 : Stmt T V ⋆ β ctx) : Stmt T V ⋆ β ctx

abbrev Stmt.typed {T : Kind → Type} {V : (κ : Kind) → Typ T κ → Type} {κ : Kind} {ctx : StmtCtx T}
  (t : Typ T κ) (s : Stmt T V κ t ctx) : Stmt T V κ t ctx :=
  s

abbrev Kernel (T : Kind → Type) (V : (κ : Kind) → Typ T κ → Type) {κ : Kind} (t : Typ T κ)
  := Stmt T V κ t ⟨none, false⟩
