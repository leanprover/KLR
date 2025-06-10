/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Basic
import KLR.NKI.Types

namespace KLR.NKI

/--
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

/--
`AccessIsType tensorTyp idxTyps resTyp` means a tensor with type `tensorTyp`
accessed by a list of indices with types `idxTyps` has type `resTyp`.
-/
inductive AccessIsType {nnat ntyp : Nat}
  : STyp nnat ntyp → List (Index.STyp nnat ntyp) → STyp nnat ntyp → Prop
  | coord_end {dim dtyp} : AccessIsType (.tensor [dim] dtyp) [.coord .int] (.dtype dtyp)
  | coord_cons {shapeHd shapeTl dtyp idxTl} :
      AccessIsType (.tensor shapeTl dtyp) idxTl resTyp
      → AccessIsType (.tensor (shapeHd :: shapeTl) dtyp) (.coord .int :: idxTl) resTyp
  -- TODO: `slice`

inductive Option.Sim (R : α → β → Prop) : Option α → Option β → Prop
  | some : R a b → Option.Sim R (.some a) (.some b)
  | none : Option.Sim R .none .none

mutual

inductive Index.IsType {nnat ntyp : Nat} : Env nnat ntyp → Index → Index.STyp nnat ntyp → Prop
  | coord {env i typ} : Expr'.IsType env i.expr typ → Index.IsType env (.coord i) (.coord typ)
  | slice {env l u step lTyp uTyp stepTyp} :
      Option.Sim (Expr'.IsType env) (l.map Expr.expr) lTyp
      → Option.Sim (Expr'.IsType env) (u.map Expr.expr) uTyp
      → Option.Sim (Expr'.IsType env) (step.map Expr.expr) stepTyp
      → Index.IsType env (.slice l u step) (.slice lTyp uTyp stepTyp)

/--
NOTE: `proj` currently has no typing rule because we don't have a notion of structures.
-/
inductive Expr'.IsType {nnat ntyp : Nat} : Env nnat ntyp → Expr' → STyp nnat ntyp → Prop
  | value {env typ value} : value.IsType env.sc typ → Expr'.IsType env (.value value) typ
  | var {env typ name} : env.var name = typ → Expr'.IsType env (.var name) typ
  | tuple {env elems typs} :
      List.Forall₂ (Expr'.IsType env) (elems.map Expr.expr) typs
      → Expr'.IsType env (.tuple elems) (.tuple typs)
  | access_tensor {env tensorExpr tensorTyp indices resTyp} :
      (idxTyps : List (Index.STyp nnat ntyp))
      -- First, the object being accessed should be a valid tensor
      → Expr'.IsType env tensorExpr.expr tensorTyp
      -- Then, indices should type check to something
      → List.Forall₂ (Index.IsType env) indices idxTyps
      -- Lastly, check what ever type the access is
      → AccessIsType tensorTyp idxTyps resTyp
      → Expr'.IsType env (.access tensorExpr indices) resTyp
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
      → List.Forall₂ (Expr'.IsType env) (args.map Expr.expr) typArgs
      → Expr'.IsType env (.call f args keywords) typRet

end

end KLR.NKI
