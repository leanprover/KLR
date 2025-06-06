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

`some n` means the given variable must be equal to `n`.
-/
def ShapeConstr (nnat : Nat) := Fin nnat → Option Nat

inductive ShapeIsType : List Nat → ShapeConstr nnat → List (SNat nnat) → Prop
  | nil {sc} : ShapeIsType [] sc []
  | cons_const {sc tl tl' hd} :
      ShapeIsType tl sc tl'
      → ShapeIsType (hd :: tl) sc (.const hd :: tl')
  | cons_param {sc tl tl' hd idx} :
      sc idx = .some hd
      → ShapeIsType tl sc tl'
      → ShapeIsType (hd :: tl) sc (.param idx :: tl')

inductive ShapeCompat : ShapeConstr nnat → List (SNat nnat) → List (SNat nnat) → Prop
  | nil {sc} : ShapeCompat sc [] []
  | cons_const {sc n tl tl'} :
      ShapeCompat sc tl tl'
      → ShapeCompat sc (.const n :: tl) (.const n :: tl')
  | cons_param_left {sc n idx tl tl'} :
      sc idx = .some n
      → ShapeCompat sc tl tl'
      → ShapeCompat sc (.param idx :: tl) (.const n :: tl')
  | cons_param_right {sc n idx tl tl'} :
      sc idx = .some n
      → ShapeCompat sc tl tl'
      → ShapeCompat sc (.const n :: tl) (.param idx :: tl')
  -- TODO: This is too strong, we need a way to constraint two parameters to be equal
  | cons_param {sc idx tl tl'} :
      ShapeCompat sc tl tl'
      → ShapeCompat sc (.param idx :: tl) (.param idx :: tl')

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

inductive Value.IsType {nnat ntyp : Nat} : Value → ShapeConstr nnat → STyp nnat ntyp → Prop
  | none {sc} : Value.IsType .none sc .none
  | bool {sc b} : Value.IsType (.bool b) sc .bool
  | int {sc n} : Value.IsType (.int n) sc .int
  | float {sc n} : Value.IsType (.float n) sc .float
  | string {sc s} : Value.IsType (.string s) sc .string
  | ellipsis {sc t} : Value.IsType .ellipsis sc t
  | tensor {sc shape dtypeStr snat dtype} :
      ShapeIsType shape sc snat
      → dtypeStr = dtype.toString
      → Value.IsType (.tensor shape dtypeStr) sc (.tensor snat dtype)

inductive BinOp.IsType {nnat ntyp : Nat} : BinOp → ShapeConstr nnat → STyp nnat ntyp → Prop
  -- logical
  | land {sc} : BinOp.IsType .land sc (.func (.tuple [.bool, .bool]) .bool)
  | lor {sc} : BinOp.IsType .lor sc (.func (.tuple [.bool, .bool]) .bool)
  -- comparison
  | eq {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .eq sc (.func (.tuple [typ1, typ2]) .bool)
  | ne {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .ne sc (.func (.tuple [typ1, typ2]) .bool)
  | lt {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .lt sc (.func (.tuple [typ1, typ2]) .bool)
  | le {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .le sc (.func (.tuple [typ1, typ2]) .bool)
  | gt {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .gt sc (.func (.tuple [typ1, typ2]) .bool)
  | ge {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .ge sc (.func (.tuple [typ1, typ2]) .bool)
  -- arithmetic, treating all operations as element wise
  | add {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .add sc (.func (.tuple [typ1, typ2]) .bool)
  | sub {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .sub sc (.func (.tuple [typ1, typ2]) .bool)
  | mul {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .mul sc (.func (.tuple [typ1, typ2]) .bool)
  | div {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .div sc (.func (.tuple [typ1, typ2]) .bool)
  | mod {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .mod sc (.func (.tuple [typ1, typ2]) .bool)
  | pow {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .pow sc (.func (.tuple [typ1, typ2]) .bool)
  | floor {sc typ1 typ2} :
      Eutsp sc typ1 typ2 → BinOp.IsType .floor sc (.func (.tuple [typ1, typ2]) .bool)
  -- TODO: broadcasting arithmetic
  -- TODO: bitwise operations


end KLR.NKI
