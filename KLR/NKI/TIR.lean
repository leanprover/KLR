/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Simplify
import KLR.NKI.Types

/-!
# Typed IR for NKI

This includes the following simplications
- Tuples are removed
- Function calls are curried and no default or keyword args are allowed
- Binnary ops become calls of constant functions
- `Stmt`s have `seq` which removed the need for `List Stmt`
- Introduce let bindings in `Stmt`
- No un-initialized variables allowed
-/

namespace KLR.NKI

namespace TIR

inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | tensor (shape : List Nat) (dtype : Core.Dtype)

/--
TODO: Manage overloading better?
-/
inductive Const where
  -- logical
  | land | lor
  -- bitwise
  | lshift | rshift | or | xor | and
  -- comparison
  | eq | ne
  | lt_int_int
  | lt_int_float
  | lt_float_int
  | lt_float_float
  | le_int_int
  | le_int_float
  | le_float_int
  | le_float_float
  | gt_int_int
  | gt_int_float
  | gt_float_int
  | gt_float_float
  | ge_int_int
  | ge_int_float
  | ge_float_int
  | ge_float_float
  -- arithmetic
  | add_int_int
  | add_int_float
  | add_float_int
  | add_float_float
  | sub_int_int
  | sub_int_float
  | sub_float_int
  | sub_float_float
  | mul_int_int
  | mul_int_float
  | mul_float_int
  | mul_float_float
  | div_int_int
  | div_int_float
  | div_float_int
  | div_float_float
  | mod_int_int
  | mod_int_float
  | mod_float_int
  | mod_float_float
  | pow_int_int
  | pow_int_float
  | pow_float_int
  | pow_float_float
  | floor_int_int
  | floor_int_float
  | floor_float_int
  | floor_float_float

mutual

inductive Index where
  | coord (i : Expr)
  | slice (l u step : Option Expr)
  | ellipsis

structure Expr where
  expr : Expr'
  pos : Pos

inductive Expr' where
  | const (const : Const)
  | value (value : Value)
  | var (name : String)
  | access (expr : Expr) (indices : List Index)
  | ifExp (test body orelse : Expr)
  | app (f : Expr) (arg : Expr)
  | typApp (f : Expr) (arg : Types.Typ)

end

inductive LHS where
  | var (name : String)
  /--
  Need `pos` here to reuse the typing rules for `Expr`.
  -/
  | access (pos : Pos) (var : String) (indices : List Index)

mutual

structure Stmt where
  stmt : Stmt'
  pos : Pos

inductive Stmt' where
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e : Expr)
  | let_ (var : String) (ty : Types.Typ) (rhs : Expr) (body : Stmt)
  | assign (lhs : LHS) (rhs : Expr)
  | ifStm (e : Expr) (thn els : Stmt)
  | forLoop (x : String) (iter : Expr) (body : Stmt)
  | breakLoop
  | continueLoop
  | seq (s1 s2 : Stmt)

end

structure Fun where
  name : String
  file : String
  line : Nat
  body : Stmt
  typArgs : List Types.Kind
  argNames : List String
  argTyps : List Types.Typ
  retTyp : Types.Typ

structure Arg where
  name : String
  value : Expr
  typ : Types.Typ

structure Kernel where
  entry : String
  typArgs : List Types.Typ
  args : List Expr
  funs : List Fun
  globals : List Arg

def mkKernelApp (entry : String) (typArgs : List Types.Typ) (args : List Expr) : Expr :=
  let pos : Pos := ⟨0, 0, none, none⟩ -- TODO: what pos to use here?
  let typApp := typArgs.foldl (fun res typ => ⟨.typApp res typ, pos⟩) ⟨.var entry, pos⟩
  args.foldl (fun res arg => ⟨.app res arg, pos⟩) typApp

/-!
# Typing Rules
-/
open Types

/--
TODO: Is the direction of folding correct?
-/
def Fun.typ (f : Fun) : Typ :=
  f.typArgs.foldl (fun typ κ => Π κ ⇒ typ)
  <| f.argTyps.foldl (fun retTyp argTyp => argTyp ⟶ retTyp) f.retTyp

structure Ctx where
  typs : TypCtx
  vars : List (String × Typ)
  retTyp : Option Typ

def Ctx.empty : Ctx :=
  ⟨[], [], none⟩

/--
  Set the type of the variable with `name` to be `typ`
-/
def Ctx.updateVar (Γ : Ctx) (name : String) (typ : Typ) : Ctx :=
  let vars := (name, typ) :: Γ.vars.filter (·.1 == name)
  {Γ with vars := vars}

def Ctx.updateVars (Γ : Ctx) (vars : List (String × Typ)) : Ctx :=
  vars.foldl (fun Γ (name, typ) => Γ.updateVar name typ) Γ

def Ctx.addTyp (Γ : Ctx) (κ : Kind) : Ctx :=
  {Γ with typs := Γ.typs,, κ}

def Ctx.setRet (Γ : Ctx) (ret : Typ) : Ctx :=
  {Γ with retTyp := some ret}

/--
TODO: the order of variable capture?
-/
def Ctx.kernelInit (globals : List Arg) (funs : List Fun) : Ctx :=
  let globals := globals.map fun arg => (arg.name, arg.typ)
  let funVars := funs.map fun f => (f.name, f.typ)
  Ctx.empty.updateVars (globals ++ funVars)

/--
TODO: this is probably not right
-/
def Ctx.addTyps (Γ : Ctx) (κs : List Kind) : Ctx :=
  {Γ with typs := Γ.typs ++ κs}

def Ctx.enterFun (Γ : Ctx) (typArgs : List Kind) (argNames : List String) (argTyps : List Typ) (retTyp : Typ) : Ctx :=
  ((Γ.addTyps typArgs).updateVars (argNames.zip argTyps)).setRet retTyp

def Ctx.addFun (Γ : Ctx) (f : Fun) : Ctx :=
  Γ.updateVar f.name f.typ

def Ctx.addFuns (Γ : Ctx) (funs : List Fun) : Ctx :=
  funs.foldl (fun Γ f => Γ.addFun f) Γ

macro:65 v:term " :ᵥ " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.TIR.Value.HasTyp) $v $α)

inductive Value.HasTyp : Value → Typ → Prop
  | none : .none :ᵥ (.prim .none)
  | bool {value : Bool} : (.bool value) :ᵥ (.prim .bool)
  | int {value : Int} : (.int value) :ᵥ (.prim .int)
  | float {value : Float} : (.float value) :ᵥ (.prim .float)
  | string {value : String} : (.string value) :ᵥ (.prim .string)
  | tensor {shape : List Nat} {dtype : Core.Dtype}
    : (.tensor shape dtype) :ᵥ (.tensor (.shape (shape.map .dim)) dtype)

@[app_unexpander Value.HasTyp]
def unexpandValueHasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasKind $v $α) => `($v :ᵥ $α)
  | _ => throw ()
-- #check Value.HasTyp.none

inductive Const.HasTyp : Const → Typ → Prop
  -- logical
  | land : Const.HasTyp .land (.prim .bool ⟶ .prim .bool ⟶ .prim .bool)
  | lor : Const.HasTyp .lor (.prim .bool ⟶ .prim .bool ⟶ .prim .bool)
  -- bitwise
  | lshift : Const.HasTyp .lshift (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | rshift : Const.HasTyp .rshift (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | or : Const.HasTyp .or (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | xor : Const.HasTyp .xor (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | and : Const.HasTyp .and (.prim .int ⟶ .prim .int ⟶ .prim .int)
  -- comparison
  | eq {α : Types.Typ} : Const.HasTyp .eq (α ⟶ α ⟶ .prim .bool)
  | ne {α : Types.Typ} : Const.HasTyp .ne (α ⟶ α ⟶ .prim .bool)
  | lt_int_int : Const.HasTyp .lt_int_int (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | lt_int_float : Const.HasTyp .lt_int_float (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | lt_float_int : Const.HasTyp .lt_float_int (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | lt_float_float : Const.HasTyp .lt_float_float (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  | le_int_int : Const.HasTyp .le_int_int (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | le_int_float : Const.HasTyp .le_int_float (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | le_float_int : Const.HasTyp .le_float_int (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | le_float_float : Const.HasTyp .le_float_float (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  | gt_int_int : Const.HasTyp .gt_int_int (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | gt_int_float : Const.HasTyp .gt_int_float (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | gt_float_int : Const.HasTyp .gt_float_int (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | gt_float_float : Const.HasTyp .gt_float_float (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  | ge_int_int : Const.HasTyp .ge_int_int (.prim .int ⟶ .prim .int ⟶ .prim .bool)
  | ge_int_float : Const.HasTyp .ge_int_float (.prim .int ⟶ .prim .float ⟶ .prim .bool)
  | ge_float_int : Const.HasTyp .ge_float_int (.prim .float ⟶ .prim .int ⟶ .prim .bool)
  | ge_float_float : Const.HasTyp .ge_float_float (.prim .float ⟶ .prim .float ⟶ .prim .bool)
  -- arithmetic
  | add_int_int : Const.HasTyp .add_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | add_int_float : Const.HasTyp .add_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | add_float_int : Const.HasTyp .add_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | add_float_float : Const.HasTyp .add_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | sub_int_int : Const.HasTyp .sub_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | sub_int_float : Const.HasTyp .sub_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | sub_float_int : Const.HasTyp .sub_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | sub_float_float : Const.HasTyp .sub_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | mul_int_int : Const.HasTyp .mul_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | mul_int_float : Const.HasTyp .mul_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | mul_float_int : Const.HasTyp .mul_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | mul_float_float : Const.HasTyp .mul_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | div_int_int : Const.HasTyp .div_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | div_int_float : Const.HasTyp .div_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | div_float_int : Const.HasTyp .div_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | div_float_float : Const.HasTyp .div_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | mod_int_int : Const.HasTyp .mod_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | mod_int_float : Const.HasTyp .mod_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | mod_float_int : Const.HasTyp .mod_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | mod_float_float : Const.HasTyp .mod_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | pow_int_int : Const.HasTyp .pow_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | pow_int_float : Const.HasTyp .pow_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | pow_float_int : Const.HasTyp .pow_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | pow_float_float : Const.HasTyp .pow_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)
  | floor_int_int : Const.HasTyp .floor_int_int (.prim .int ⟶ .prim .int ⟶ .prim .int)
  | floor_int_float : Const.HasTyp .floor_int_float (.prim .int ⟶ .prim .float ⟶ .prim .float)
  | floor_float_int : Const.HasTyp .floor_float_int (.prim .float ⟶ .prim .int ⟶ .prim .float)
  | floor_float_float : Const.HasTyp .floor_float_float (.prim .float ⟶ .prim .float ⟶ .prim .float)

macro:65 Γ:term " ⊢ " e:term " :ₑ " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.TIR.Expr.HasTyp) $Γ $e $α)
macro:65 Γ:term " ⊢ " e:term " :ₑ' " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.TIR.Expr'.HasTyp) $Γ $e $α)

mutual

inductive Option.HasIntTyp : Ctx → Option Expr → Prop
  | some {Γ : Ctx} {e : Expr} : (Γ ⊢ e :ₑ .prim .int) → Option.HasIntTyp Γ (.some e)
  | none {Γ : Ctx} : Option.HasIntTyp Γ .none

/--
TODO:
- How do we support operators like `shapeAppend`?
- Ellipsis
-/
inductive Index.HasTyp : Ctx → Typ → List Index → Typ → Prop
  | coord_end {Γ : Ctx} {dim : Typ} {dtyp : Core.Dtype} {i : Expr}
    : (Γ.typs ⊢⋆ dim : .dim)
      → (Γ ⊢ i :ₑ .prim .int)
      → Index.HasTyp Γ (.tensor (.shape [dim]) dtyp) [.coord i] (.prim <| .dtype dtyp)
  | coord_last {Γ : Ctx} {shapeHd : Typ} {shapeTl : List Typ} {dtyp : Core.Dtype} {i : Expr}
    : (Γ.typs ⊢⋆ shapeHd : .dim)
      → (∀ shape ∈ shapeTl, Γ.typs ⊢⋆ shape : .dim)
      → (Γ ⊢ i :ₑ .prim .int)
      → Index.HasTyp Γ (.tensor (.shape <| shapeHd :: shapeTl) dtyp) [.coord i] (.tensor (.shape shapeTl) dtyp)
  | coord_cons {Γ : Ctx} {shapeHd : Typ} {shapeTl : List Typ} {dtyp : Core.Dtype}
    {idxHd : Expr} {idxTl : List Index} {t : Typ}
    : (Γ.typs ⊢⋆ shapeHd : .dim)
      → (Γ ⊢ idxHd :ₑ .prim .int)
      → Index.HasTyp Γ (.tensor (.shape shapeTl) dtyp) idxTl t
      → Index.HasTyp Γ (.tensor (.shape <| shapeHd :: shapeTl) dtyp) (.coord idxHd :: idxTl) t
  | slice_end {Γ : Ctx} {inDim outDim : Typ} {dtyp : Core.Dtype} {l u step : Option Expr}
    : (Γ.typs ⊢⋆ inDim : .dim) → (Γ.typs ⊢⋆ outDim : .dim)
      → Option.HasIntTyp Γ l → Option.HasIntTyp Γ u → Option.HasIntTyp Γ step
      → Index.HasTyp Γ (.tensor (.shape [inDim]) dtyp) [.slice l u step] (.tensor (.shape [outDim]) dtyp)
  | slice_cons_last {Γ : Ctx} {inShapeHd outDim : Typ} {inShapeTl : List Typ} {dtyp : Core.Dtype}
    {l u step : Option Expr} {idxTl : List Index}
    : (Γ.typs ⊢⋆ inShapeHd : .dim) → (Γ.typs ⊢⋆ outDim : .dim)
      → Option.HasIntTyp Γ l → Option.HasIntTyp Γ u → Option.HasIntTyp Γ step
      → Index.HasTyp Γ (.tensor (.shape inShapeTl) dtyp) idxTl (.prim <| .dtype dtyp)
      → Index.HasTyp Γ
          (.tensor (.shape <| inShapeHd :: inShapeTl) dtyp)
          (.slice l u step :: idxTl)
          (.tensor (.shape [outDim]) dtyp)
  | slice_cons_cons {Γ : Ctx} {inShapeHd outShapeHd : Typ} {inShapeTl : List Typ} {dtyp : Core.Dtype}
    {l u step : Option Expr} {idxTl : List Index}
    : (Γ.typs ⊢⋆ inShapeHd : .dim) → (∀ shape ∈ inShapeTl, Γ.typs ⊢⋆ shape : .dim) → (Γ.typs ⊢⋆ outShapeHd : .dim)
      → Option.HasIntTyp Γ l → Option.HasIntTyp Γ u → Option.HasIntTyp Γ step
      → Index.HasTyp Γ
          (.tensor (.shape <| inShapeHd :: inShapeTl) dtyp)
          (.slice l u step :: idxTl)
          (.tensor (.shape <| outShapeHd :: inShapeTl) dtyp)
  | slice_cons_more {Γ : Ctx} {inShapeHd outShapeHd : Typ} {inShapeTl outShapeTl : List Typ} {dtyp : Core.Dtype}
    {l u step : Option Expr} {idxTl : List Index}
    : (Γ.typs ⊢⋆ inShapeHd : .dim) → (Γ.typs ⊢⋆ outShapeHd : .dim)
      → Option.HasIntTyp Γ l → Option.HasIntTyp Γ u → Option.HasIntTyp Γ step
      → Index.HasTyp Γ (.tensor (.shape inShapeTl) dtyp) idxTl (.tensor (.shape outShapeTl) dtyp)
      → Index.HasTyp Γ
          (.tensor (.shape <| inShapeHd :: inShapeTl) dtyp)
          (.slice l u step :: idxTl)
          (.tensor (.shape <| outShapeHd :: outShapeTl) dtyp)

inductive Expr.HasTyp : Ctx → Expr → Typ → Prop
  | mk {Γ : Ctx} {e : Expr} {t : Typ} : (Γ ⊢ e.expr :ₑ' t) → Γ ⊢ e :ₑ t

inductive Expr'.HasTyp : Ctx → Expr' → Typ → Prop
  | const {Γ : Ctx} {const : Const} {t : Typ} : const.HasTyp t → Γ ⊢ .const const :ₑ' t
  | value {Γ : Ctx} {value : Value} {t : Typ} : (value :ᵥ t) → Γ ⊢ .value value :ₑ' t
  | var {Γ : Ctx} {name : String} {t : Typ} : (Γ.typs ⊢⋆ t : .typ) → (name, t) ∈ Γ.vars → Γ ⊢ .var name :ₑ' t
  | access {Γ : Ctx} {expr : Expr} {indices : List Index} {t r : Typ}
    : (Γ ⊢ expr :ₑ t)
      → Index.HasTyp Γ t indices r
      → Γ ⊢ .access expr indices :ₑ' r
  | ifExp {Γ : Ctx} {test body orelse : Expr} {t : Typ}
    : (Γ ⊢ test :ₑ .prim .bool)
      → (Γ ⊢ body :ₑ t)
      → (Γ ⊢ orelse :ₑ t)
      → Γ ⊢ .ifExp test body orelse :ₑ' t
  | app {Γ : Ctx} {f : Expr} {arg : Expr} {dom ran : Typ}
    : (Γ ⊢ f :ₑ dom ⟶ ran)
      → (Γ ⊢ arg :ₑ dom)
      → Γ ⊢ .app f arg :ₑ' ran
  | typApp {Γ : Ctx} {f : Expr} {arg : Typ} {κ : Kind} {t : Typ}
    : (Γ ⊢ f :ₑ Π κ ⇒ t)
      → (Γ.typs ⊢⋆ arg : κ)
      → Γ.addTyp κ ⊢ .typApp f arg :ₑ' t

end

@[app_unexpander Expr.HasTyp]
def unexpandExprHasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $e $α) => `($Γ ⊢ $e :ₑ $α)
  | _ => throw ()

@[app_unexpander Expr'.HasTyp]
def unexpandExpr'HasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $e $α) => `($Γ ⊢ $e :ₑ' $α)
  | _ => throw ()

-- #check Expr.HasTyp ⟨[], [], none⟩ ⟨.value <| .bool true, ⟨0, 0, none, none⟩⟩ (.prim .bool)
-- #check Expr'.HasTyp ⟨[], [], none⟩ (.value <| .bool true) (.prim .bool)

macro:65 Γ:term " ⊢ " s:term " :ₛ " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.TIR.Stmt.HasTyp) $Γ $s $α)
macro:65 Γ:term " ⊢ " s:term " :ₛ' " α:term : term =>
  `($(Lean.mkIdent `KLR.NKI.TIR.Stmt'.HasTyp) $Γ $s $α)

mutual

inductive Stmt.HasTyp : Ctx → Stmt → Typ → Prop
  | mk {Γ : Ctx} {t : Typ} {stmt : Stmt'} {pos : Pos}
    : (Γ ⊢ stmt :ₛ' α) → Γ ⊢ {stmt, pos} :ₛ t

inductive Stmt'.HasTyp : Ctx → Stmt' → Typ → Prop
  | expr {Γ : Ctx} {e : Expr} {t : Typ} : (Γ ⊢ e :ₑ t) → Γ ⊢ .expr e :ₛ' t
  -- TODO: `assert`
  | ret {Γ : Ctx} {e : Expr} {t : Typ} : Γ.retTyp = some t → (Γ ⊢ e :ₑ t) → Γ ⊢ .ret e :ₛ' .prim .none
  | let_ {Γ : Ctx} {var : String} {ty : Typ} {rhs : Expr} {body : Stmt} {t : Typ}
    : (Γ ⊢ rhs :ₑ ty)
      → (Γ.updateVar var ty ⊢ body :ₛ t)
      → Γ ⊢ .let_ var ty rhs body :ₛ' t
  | assign_var {Γ : Ctx} {name : String} {rhs : Expr} {t : Typ}
    : (name, t) ∈ Γ.vars
      → (Γ ⊢ rhs :ₑ t)
      → Γ ⊢ .assign (.var name) rhs :ₛ' .prim .none
  | assign_access {Γ : Ctx} {pos : Pos} {var : String} {indices : List Index} {rhs : Expr} {t : Typ}
    : (var, t) ∈ Γ.vars
      → (Γ ⊢ .access ⟨.var var, pos⟩ indices :ₑ' t)
      → Γ ⊢ .assign (.access pos var indices) rhs :ₛ' .prim .none
  | ifStm {Γ : Ctx} {e : Expr} {thn els : Stmt} {t : Typ}
    : (Γ ⊢ e :ₑ .prim .bool)
      → (Γ ⊢ thn :ₛ t)
      → (Γ ⊢ els :ₛ t)
      → Γ ⊢ .ifStm e thn els :ₛ' t
  -- TODO: Cannot type-check `forLoop` right now because we don't have an iterator type
  | breakLoop {Γ : Ctx} : Γ ⊢ .breakLoop :ₛ' .prim .none
  | continueLoop {Γ : Ctx} : Γ ⊢ .continueLoop :ₛ' .prim .none
  | seq {Γ : Ctx} {s1 s2 : Stmt} {t1 t2 : Typ}
    : (Γ ⊢ s1 :ₛ t1)
      → (Γ ⊢ s2 :ₛ t2)
      → Γ ⊢ .seq s1 s2 :ₛ' t2

end

@[app_unexpander Stmt.HasTyp]
def unexpandStmtHasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $s $α) => `($Γ ⊢ $s :ₛ $α)
  | _ => throw ()

@[app_unexpander Stmt'.HasTyp]
def unexpandStmt'HasTyp : Lean.PrettyPrinter.Unexpander
  | `($_HasTyp $Γ $s $α) => `($Γ ⊢ $s :ₛ' $α)
  | _ => throw ()

-- #check Stmt.HasTyp ⟨[], [], none⟩ ⟨.expr ⟨.value <| .bool true, ⟨0, 0, none, none⟩⟩, ⟨0, 0, none, none⟩⟩ (.prim .bool)
-- #check Stmt'.HasTyp ⟨[], [], none⟩ (.expr ⟨.value <| .bool true, ⟨0, 0, none, none⟩⟩) (.prim .bool)

inductive Fun.HasTyp (Γ : Ctx) : Fun → Typ → Prop
  | mk {name : String} {file : String} {line : Nat} {body : Stmt}
    {typArgs : List Kind} {argNames : List String} {argTyps : List Typ} {retTyp : Typ} {t : Typ}
    : (Γ.enterFun typArgs argNames artTyps retTyp ⊢ body :ₛ t)
      → Fun.HasTyp Γ {name, file, line, body, typArgs, argNames, argTyps, retTyp} t

inductive Kernel.HasTyp : Kernel → Typ → Prop
  | mk {entry : String} {typArgs : List Typ} {args : List Expr} {funs : List Fun} {globals : List Arg}
    {funTyps : List Typ} {t : Typ}
    : (∀ arg ∈ globals, .empty ⊢ arg.value :ₑ arg.typ) -- TODO: do globals depend on prior globals?
      → List.Forall₂ (fun f typ => Fun.HasTyp (Ctx.kernelInit globals funs) f typ) funs funTyps
      → (Ctx.kernelInit globals funs ⊢ mkKernelApp entry typArgs args :ₑ t)
      → Kernel.HasTyp {entry, typArgs, args, funs, globals} t

end TIR
