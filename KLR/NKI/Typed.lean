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

import Lean
import TensorLib.Tensor

/-!
# Type System For NKI And An Instrinsically Typed AST

TODO: Subtyping
-/

namespace KLR.NKI.Typed

inductive Kind
  | size
  | shape
  | dtype
  | type
  | arrow (κ ι : Kind)
notation "⋆" => Kind.type
infixr:55 " ⟶⋆ " => Kind.arrow

inductive Prim
  | none
  | bool
  | int
  | float
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
`t1[t2] ↦ t3` means substituting `t2` for the top-level bound variable in `t1` reduces to `t3`.
-/
macro:100 t1:term "[" t2:term "]" " ↦ " t3:term : term =>
  `($(Lean.mkIdent `Typ.Subst) $t1 $t2 $t3)

mutual

inductive Typ.SubstList {T : Kind → Type} : {κ ι : Kind} → List (T κ → Typ T ι) → Typ T κ → List (Typ T ι) → Prop
  | nil {t} : Typ.SubstList [] t []
  | cons {t1h t1t t t2h t2t}
    : (t1h[t] ↦ t2h) → Typ.SubstList t1t t t2t
      → Typ.SubstList (t1h :: t1t) t (t2h :: t2t)
/--
Relational type substitution rules
-/
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

-- def arr {T} : T ⋆ → Typ T ⋆ := fun t => .var t ⟶ .prim .int
-- example {T} : (@arr T)[.prim .int] ↦ .prim .int ⟶ .prim .int :=
--   .arrow .var_eq .prim

-- def m {T} : T .size → Typ T .shape := fun m => .shape [.var m, .size 10]
-- example {T} : (m (T := T))[.size 0] ↦ .shape [.size 0, .size 10] :=
--   .shape --(sh := [.var, fun _ => .size 10]) (sh' := [.size 0, .size 10])
--     (.cons .var_eq (.cons (.size) .nil))

-- #check (Types.Subst.var_eq : Types.var[.prim .none] ↦ (.prim .none))
-- #check (fun _ _ => .var_ne : (T : Kind → Type) → (y : T ⋆) → (fun _ => .var y)[.prim .none] ↦ (.var y))
-- #check (.var_eq : (fun x => .var x)[.prim .none] ↦ (.prim .none))

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
  | ifExp {α : Typ T ⋆} (test : Expr T V ⋆ (.prim .int)) (body orelse : Expr T V ⋆ α) : Expr T V ⋆ α
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
  | abs {α β ret} (body : V ⋆ α → Stmt T V ⋆ β ⟨some β, false⟩) : Stmt T V ⋆ (α ⟶ β) ⟨ret, false⟩
  | typAbs {κ ι : Kind}
    (t : T κ → Typ T ι)
    (body : (arg : T κ) → Stmt T V ι (t arg) ⟨none, false⟩)
    : Stmt T V (κ ⟶⋆ ι) (.all t) ⟨none, false⟩
  | ret {α loop} (e : Expr T V ⋆ α) : Stmt T V ⋆ α ⟨some α, loop⟩
  | let_ {β ctx} {α : Typ T ⋆} (rhs : Expr T V ⋆ α)
    (body : V ⋆ α → Stmt T V ⋆ β ctx) : Stmt T V ⋆ β ctx
  | ifStm {α ctx} (e : Expr T V ⋆ (.prim .bool)) (thn els : Stmt T V ⋆ α ctx) : Stmt T V ⋆ α ctx
  | forLoop {α β ret loop} (x : V ⋆ α) (iter : Expr T V ⋆ (.iter α))
    (body : V ⋆ α → Stmt T V ⋆ β ⟨ret, true⟩) : Stmt T V ⋆ β ⟨ret, loop⟩
  | breakLoop {ret} : Stmt T V ⋆ (.prim .none) ⟨ret, true⟩
  | continueLoop {ret} : Stmt T V ⋆ (.prim .none) ⟨ret, true⟩
  | seq {α β ctx} (s1 : Stmt T V ⋆ α ctx) (s2 : Stmt T V ⋆ β ctx) : Stmt T V ⋆ β ctx

/-!
# Parser
-/

declare_syntax_cat nki_type
syntax "None" : nki_type
syntax "int" : nki_type

declare_syntax_cat nki_expr

syntax "(" nki_expr ")" : nki_expr

-- Values
syntax "None" : nki_expr
syntax "True" : nki_expr
syntax "Flase" : nki_expr
syntax num : nki_expr -- int
syntax num "." num : nki_expr -- float
syntax str : nki_expr
-- TODO: tensor

-- Expr
syntax ident : nki_expr -- var
syntax nki_expr " if " nki_expr " else " nki_expr : nki_expr
syntax nki_expr "(" nki_expr,* ")" : nki_expr -- app
syntax nki_expr "[" nki_expr,* "]" "(" nki_expr ")" : nki_expr -- typApp + app
-- TODO: built-ins

declare_syntax_cat nki_stmt

syntax "def " ident ("[" ident,+ "]")? "(" (ident " : " nki_type),* ")" " -> " nki_type ": " nki_stmt " end" : nki_stmt
syntax "return " nki_expr : nki_stmt
syntax nki_expr : nki_stmt
syntax "let " ident " = " nki_expr "; " nki_stmt : nki_stmt
syntax "if " nki_expr ": " nki_stmt " end" : nki_stmt
syntax "if " nki_expr ": " nki_stmt " else " nki_stmt " end" : nki_stmt
syntax "for " ident " in " nki_expr ": " nki_stmt " end" : nki_stmt
syntax "break" : nki_stmt
syntax "continue" : nki_stmt
syntax nki_stmt "; " nki_stmt : nki_stmt

open Lean Macro Meta

def expandNKIType : Syntax → MacroM (TSyntax `term)
  | `(nki_type| None) => `(Typ.prim Prim.none)
  | `(nki_type| int) => `(Typ.prim Prim.int)
  | _ => throwUnsupported

macro "ty⟪" t:nki_type "⟫" : term => expandNKIType t

def expandNKIExpr : Syntax → MacroM (TSyntax `term)
  | `(nki_expr| $i:ident) => `(Expr.var $i)
  | `(nki_expr| $n:num) => `(Expr.value <| Value.int $n)
  | _ => throwUnsupported

macro "⟪" e:nki_expr "⟫" : term => expandNKIExpr e

partial def expandNKIStmt : Syntax → MacroM (TSyntax `term)
  | `(nki_stmt| def $name $[[ $[$typArgs],* ]]? ( $[ $args : $typs ],* ) -> $returns : $body end) => do
    (args.zip typs).foldrM
      (fun (arg, typ) body =>
        `(Stmt.abs (α := ty⟪ $typ ⟫) (fun $arg => $body)))
      (← expandNKIStmt body)
  | `(nki_stmt| return $e) => `(Stmt.ret (⟪ $e ⟫))
  | _ => throwUnsupported

macro "〚" s:nki_stmt "〛" : term => expandNKIStmt s

def kernel {T V} : @Stmt T V ⋆ (.prim .int ⟶ .prim .int) ⟨none, false⟩ :=
〚
def foo(a : int) -> int:
  return 0
end
〛

#check 〚
def foo(a : int) -> int:
  return a
end
〛
