/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Basic
import KLR.NKI.Types
import Mathlib.Logic.Function.Basic

namespace KLR.NKI

/--
TODO: properly handle updating environments in function calls and let-bindings

Constraints for SNat variables.

`none` means no constraint.

`some (.const n)` means the given variable must be equal to constant `n`.
`some (.param idx)` means the given variable must be equal to another parameter `idx`.
-/
inductive ShapeConstrVal (nnat : Nat)
  | const : Nat → ShapeConstrVal nnat
  | param : Fin nnat → ShapeConstrVal nnat

def ShapeConstr (nnat : Nat) :=
  Fin nnat → Option (ShapeConstrVal nnat)

inductive ShapeIsType : ShapeConstr nnat → List Nat → List (SNat nnat) → Prop
  | nil {sc} : ShapeIsType sc [] []
  | cons_const {sc tl tl' hd} :
      ShapeIsType sc tl tl'
      → ShapeIsType sc (hd :: tl) (.const hd :: tl')
  | cons_param {sc tl tl' hd idx} :
      sc idx = .some (.const hd)
      → ShapeIsType sc tl tl'
      → ShapeIsType sc (hd :: tl) (.param idx :: tl')

inductive ShapeCompat : ShapeConstr nnat → List (SNat nnat) → List (SNat nnat) → Prop
  | nil {sc} : ShapeCompat sc [] []
  | cons_const {sc n tl tl'} :
      ShapeCompat sc tl tl'
      → ShapeCompat sc (.const n :: tl) (.const n :: tl')
  | cons_const_left {sc n idx tl tl'} :
      sc idx = .some (.const n)
      → ShapeCompat sc tl tl'
      → ShapeCompat sc (.const n :: tl) (.param idx :: tl')
  | cons_const_right {sc n idx tl tl'} :
      sc idx = .some (.const n)
      → ShapeCompat sc tl tl'
      → ShapeCompat sc (.param idx :: tl) (.const n :: tl')
  | cons_param_same {sc idx tl tl'} :
      ShapeCompat sc tl tl'
      → ShapeCompat sc (.param idx :: tl) (.param idx :: tl')
  | cons_param_diff {sc idx1 idx2 tl tl'} :
      sc idx1 = .some (.param idx2) ∨ sc idx2 = .some (.param idx1)
      → ShapeCompat sc tl tl'
      → ShapeCompat sc (.param idx1 :: tl) (.param idx2 :: tl')

/--
Two types can be equivalent up to shape parameters (`Eutsp`).
-/
inductive Eutsp : ShapeConstr nnat → STyp nnat ntyp → STyp nnat ntyp → Prop
  | refl {sc typ} : Eutsp sc typ typ
  | tuple {sc typs1 typs2} :
      (∀ typ12 ∈ typs1.zip typs2, Eutsp sc typ12.1 typ12.2) → Eutsp sc (.tuple typs1) (.tuple typs2)
  | tensor {sc shape1 shape2 dtype} :
      ShapeCompat sc shape1 shape2 → Eutsp sc (.tensor shape1 dtype) (.tensor shape2 dtype)
  | func {sc dom ran dom' ran'} :
      Eutsp sc dom dom' → Eutsp sc ran ran' → Eutsp sc (.func dom ran) (.func dom ran')

inductive Value.IsType {nnat ntyp : Nat} : ShapeConstr nnat → Value → STyp nnat ntyp → Prop
  | none {sc} : Value.IsType sc .none .none
  | bool {sc b} : Value.IsType sc (.bool b) .bool
  | int {sc n} : Value.IsType sc (.int n) .int
  | float {sc n} : Value.IsType sc (.float n) .float
  | string {sc s} : Value.IsType sc (.string s) .string
  | ellipsis {sc t} : Value.IsType sc .ellipsis t
  | tensor {sc shape dtypeStr snat dtype} :
      ShapeIsType sc shape snat
      → dtypeStr = dtype.toString
      → Value.IsType sc (.tensor shape dtypeStr) (.tensor snat dtype)

inductive BinOp.IsType {nnat ntyp : Nat} : ShapeConstr nnat → BinOp → STyp nnat ntyp → Prop
  -- logical
  | land {sc} : BinOp.IsType sc .land (.func (.tuple [.bool, .bool]) .bool)
  | lor {sc} : BinOp.IsType sc .lor (.func (.tuple [.bool, .bool]) .bool)
  -- comparison
  | eq {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .eq (.func (.tuple [typ1, typ2]) .bool)
  | ne {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .ne (.func (.tuple [typ1, typ2]) .bool)
  | lt {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .lt (.func (.tuple [typ1, typ2]) .bool)
  | le {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .le (.func (.tuple [typ1, typ2]) .bool)
  | gt {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .gt (.func (.tuple [typ1, typ2]) .bool)
  | ge {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .ge (.func (.tuple [typ1, typ2]) .bool)
  -- arithmetic, treating all operations as element wise
  -- TODO: is it ok to set the output to `typ` in these cases?
  -- TODO: limit these to numeric types
  | add {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .add (.func (.tuple [typ1, typ2]) typ1)
  | sub {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .sub (.func (.tuple [typ1, typ2]) typ1)
  | mul {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .mul (.func (.tuple [typ1, typ2]) typ1)
  | div {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .div (.func (.tuple [typ1, typ2]) typ1)
  | mod {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .mod (.func (.tuple [typ1, typ2]) typ1)
  | pow {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .pow (.func (.tuple [typ1, typ2]) typ1)
  | floor {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .floor (.func (.tuple [typ1, typ2]) typ1)
  -- bitwise operations
  | or {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .or (.func (.tuple [typ1, typ2]) typ1)
  | xor {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .xor (.func (.tuple [typ1, typ2]) typ1)
  | and {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .and (.func (.tuple [typ1, typ2]) typ1)
  -- TODO: what should the rhs be for shift?
  | lshift {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .lshift (.func (.tuple [typ1, typ2]) typ1)
  | rshift {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType sc .rshift (.func (.tuple [typ1, typ2]) typ1)

def VarEnv (nnat ntyp : Nat) := String → STyp nnat ntyp

structure Env (nnat ntyp : Nat) where
  sc : ShapeConstr nnat
  var : VarEnv nnat ntyp

inductive Index.STyp (nnat ntyp : Nat)
  | coord (i : NKI.STyp nnat ntyp)
  | slice (l u step : Option (NKI.STyp nnat ntyp))

inductive Option.IsInt {nnat ntyp : Nat} : Option (STyp nnat ntyp) → Prop
  | some : Option.IsInt (.some .int)
  | none : Option.IsInt .none

inductive TensorTyp (nnat : Nat)
  | elem (dtyp : Core.Dtype)
  | tensor (shape : List (SNat nnat)) (dtyp : Core.Dtype)

def TensorTyp.cons {nnat} (hd : SNat nnat) : TensorTyp nnat → TensorTyp nnat
  | .elem dtyp => .tensor [hd] dtyp
  | .tensor shape dtyp => .tensor (hd :: shape) dtyp
infixr:60 " ::ₜ " => TensorTyp.cons

/--
`AccessIsType tensorTyp idxTyps resTyp` means a tensor with type `tensorTyp`
accessed by a list of indices with types `idxTyps` has type `resTyp`.
-/
inductive AccessIsType {nnat ntyp : Nat}
  : STyp nnat ntyp → List (Index.STyp nnat ntyp) → TensorTyp nnat → Prop
  | coord_end {dim dtyp} : AccessIsType (.tensor [dim] dtyp) [.coord .int] (.elem dtyp)
  | coord_cons {shapeHd shapeTl dtyp idxTl} :
      AccessIsType (.tensor shapeTl dtyp) idxTl resTyp
      → AccessIsType (.tensor (shapeHd :: shapeTl) dtyp) (.coord .int :: idxTl) resTyp
  -- TODO: how should we enforce the output dimension?
  | slice_end {inDim outDim dtyp l u step} :
      Option.IsInt l → Option.IsInt u → Option.IsInt step
      → AccessIsType (.tensor [inDim] dtyp) [.slice l u step] (.tensor [outDim] dtyp)
  | slice_cons {inShapeHd inShapeTl outShapeHd dtyp l u step idxTl tlTyp} :
      Option.IsInt l → Option.IsInt u → Option.IsInt step
      → AccessIsType (.tensor inShapeTl dtyp) idxTl tlTyp
      → AccessIsType
          (.tensor (inShapeHd :: inShapeTl) dtyp)
          (.slice l u step :: idxTl)
          (outShapeHd ::ₜ tlTyp)

/-!
Mutual inductions are causing some pains here.

Forexample, we cannot just use `List.Forall₂` for reasons similar to
[this](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20requiring.20proofs.20on.20inductive.20constructors)
-/

mutual

inductive List.IndexIsType {nnat ntyp : Nat} : Env nnat ntyp → List Index → List (Index.STyp nnat ntyp) → Prop
  | nil {env} : List.IndexIsType env [] []
  | cons {env idx typ idxes typs} :
      Index.IsType env idx typ
      → List.IndexIsType env idxes typs
      → List.IndexIsType env (idx :: idxes) (typ :: typs)

inductive List.Expr'IsType {nnat ntyp : Nat} : Env nnat ntyp → List Expr' → List (STyp nnat ntyp) → Prop
  | nil {env} : List.Expr'IsType env [] []
  | cons {env expr typ exprs typs} :
      Expr'.IsType env expr typ
      → List.Expr'IsType env idxes typs
      → List.Expr'IsType env (expr :: exprs) (typ :: typs)

inductive Option.Expr'IsType {nnat ntyp} : Env nnat ntyp → Option Expr' → Option (STyp nnat ntyp) → Prop
  | some : Expr'.IsType env expr typ → Option.Expr'IsType env (.some expr) (.some typ)
  | none : Option.Expr'IsType env .none .none

inductive Index.IsType {nnat ntyp : Nat} : Env nnat ntyp → Index → Index.STyp nnat ntyp → Prop
  | coord {env i typ} : Expr'.IsType env i.expr typ → Index.IsType env (.coord i) (.coord typ)
  | slice {env l u step lTyp uTyp stepTyp} :
      Option.Expr'IsType env (l.map Expr.expr) lTyp
      → Option.Expr'IsType env (u.map Expr.expr) uTyp
      → Option.Expr'IsType env (step.map Expr.expr) stepTyp
      → Index.IsType env (.slice l u step) (.slice lTyp uTyp stepTyp)

/--
NOTE: `proj` currently has no typing rule because we don't have a notion of structures.
-/
inductive Expr'.IsType {nnat ntyp : Nat} : Env nnat ntyp → Expr' → STyp nnat ntyp → Prop
  | value {env typ value} : value.IsType env.sc typ → Expr'.IsType env (.value value) typ
  | var {env typ name} : env.var name = typ → Expr'.IsType env (.var name) typ
  | tuple {env elems typs} :
      List.Expr'IsType env (elems.map Expr.expr) typs
      → Expr'.IsType env (.tuple elems) (.tuple typs)
  | access_tensor_elem {env tensorExpr tensorTyp indices} :
      (idxTyps : List (Index.STyp nnat ntyp))
      -- First, the object being accessed should be a valid tensor
      → Expr'.IsType env tensorExpr.expr tensorTyp
      -- Then, indices should type check to something
      → List.IndexIsType env indices idxTyps
      -- Lastly, check what ever type the access is
      → AccessIsType tensorTyp idxTyps (.elem dtyp)
      → Expr'.IsType env (.access tensorExpr indices) (.dtype dtyp)
  | access_tensor_tensor {env tensorExpr tensorTyp indices shape} :
      (idxTyps : List (Index.STyp nnat ntyp))
      -- First, the object being accessed should be a valid tensor
      → Expr'.IsType env tensorExpr.expr tensorTyp
      -- Then, indices should type check to something
      → List.IndexIsType env indices idxTyps
      -- Lastly, check what ever type the access is
      → AccessIsType tensorTyp idxTyps (.tensor shape dtyp)
      → Expr'.IsType env (.access tensorExpr indices) (.tensor shape dtyp)
  | binOp {env op expL expR typL typR typRet} :
      op.IsType env.sc (.func (.tuple [typL, typR]) typRet)
      → Expr'.IsType env expL.expr typL
      → Expr'.IsType env expR.expr typR
      → Expr'.IsType env (.binOp op expL expR) typRet
  | ifExp {env test body orelse} :
      Expr'.IsType env test.expr .bool
      → Expr'.IsType env (.ifExp test body orelse) .none
  | call {env f args keywords typArgs typRet} :
      -- Note: We expect kwargs and default to be turned into positional arguments already.
      Expr'.IsType env f.expr (.func (.tuple typArgs) typRet)
      → List.Expr'IsType env (args.map Expr.expr) typArgs
      → Expr'.IsType env (.call f args keywords) typRet

end

def Env.addVar (env : Env nnat ntyp) (name : String) (typ : STyp nnat ntyp) : Env nnat ntyp :=
  {env with var := Function.update env.var name typ}

mutual

inductive Stmt'.IsType {nnat ntyp : Nat} : Env nnat ntyp → Stmt' → STyp nnat ntyp → Prop
  | expr {env e typ} :
      Expr'.IsType env e.expr typ
      → Stmt'.IsType env (.expr e) typ
  | assert {env e} :
      Expr'.IsType env e.expr .bool
      -- Should this type to none?
      → Stmt'.IsType env (.assert e) .none
  | ret {env e typ} :
      Expr'.IsType env e.expr typ
      → Stmt'.IsType env (.ret e) typ
  | assign_no_type {env x e typ} :
      Expr'.IsType env e.expr typ
      → Expr'.IsType env x.expr typ
      → Stmt'.IsType env (.assign x .none (some e)) .none
  | assign_decl {env x typ} :
      Expr'.IsType env x.expr typ
      → Stmt'.IsType env (.assign x .none .none) .none
  | if_stmt {env e thn thnTyp els elsTyp} :
      Expr'.IsType env e.expr .bool
      → List.Stmt'IsType env thn thnTyp
      → List.Stmt'IsType env els elsTyp
      → Stmt'.IsType env (.ifStm e thn els) .none
  -- TODO: for loops
  | break_loop {env} :
      Stmt'.IsType env .breakLoop .none
  | continue_loop {env} :
      Stmt'.IsType env .continueLoop .none

-- Add typing rules for lists of statements
inductive List.Stmt'IsType {nnat ntyp : Nat} : Env nnat ntyp → List Stmt → STyp nnat ntyp → Prop
  | nil {env} : List.Stmt'IsType env [] .none
  | singleton {env stmt typ} :
      Stmt'.IsType env stmt.stmt typ
      → List.Stmt'IsType env [stmt] typ
  | cons {env stmt stmts hdTyp tlTyp} :
      Stmt'.IsType env stmt.stmt hdTyp
      → List.Stmt'IsType env stmts tlTyp
      → List.Stmt'IsType env (stmt :: stmts) tlTyp

end

inductive List.ParamIsType {nnat ntyp : Nat} : Env nnat ntyp → List Param → List (STyp nnat ntyp) → Prop
  | nil {env} : List.ParamIsType env [] []
  | cons_none {env name params typ typs} :
      List.ParamIsType env params typs
      → List.ParamIsType env (⟨name, .none⟩ :: params) (typ :: typs)
  | cons_some {env name param params typ typs} :
      Expr'.IsType env param.expr typ
      → List.ParamIsType env params typs
      → List.ParamIsType env (⟨name, .some param⟩ :: params) (typ :: typs)

def Env.addVars (env : Env nnat ntyp) (names : List String) (typs : List (STyp nnat ntyp)) : Env nnat ntyp :=
  match names, typs with
  | [], [] => env
  | nameHd :: nameTl, typsHd :: typsTl => Env.addVars (env.addVar nameHd typsHd) nameTl typsTl
  | _, _ => env

inductive Fun.IsType {nnat ntyp : Nat} : Env nnat ntyp → Fun → STyp nnat ntyp → Prop
  | mk {name file line body args argTyps retTyp} :
      List.ParamIsType env args argTyps
      → List.Stmt'IsType (env.addVars (args.map Param.name) argTyps) body retTyp
      → Fun.IsType env ⟨name, file, line, body, args⟩ (.func (.tuple argTyps) retTyp)

inductive Kernel.IsType' {nnat ntyp : Nat} : Env nnat ntyp → Kernel → STyp nnat ntyp → Prop
  | mk {env entry funs args globals globalTyps funTyps entryFun argTyps retTyp newEnv} :
      -- Type check the global vars first
      List.Forall₂ (Expr'.IsType env) (globals.map (Expr.expr ∘ Arg.value)) globalTyps
      -- Update the environment
      → newEnv = env.addVars (globals.map Arg.name) globalTyps
      -- Type check all functions
      → List.Forall₂ (Fun.IsType newEnv) funs funTyps
      -- Find the entry function
      → funs.find? (·.name == entry) = .some entryFun
      -- Type check entry function
      → Fun.IsType newEnv entryFun (.func (.tuple argTyps) retTyp)
      -- Type check arguments
      → List.Forall₂ (Expr'.IsType newEnv) (args.map (Expr.expr ∘ Arg.value)) argTyps
      → Kernel.IsType' env ⟨entry, funs, args, globals⟩ retTyp

def Kernel.IsType {nnat ntyp : Nat} (k : Kernel) (typ : STyp nnat ntyp) : Prop :=
  ∃ env, k.IsType' env typ

end KLR.NKI
