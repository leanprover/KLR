/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import Mathlib.Logic.Function.Basic
import KLR.NKI.Basic
import KLR.NKI.Types

namespace KLR.NKI

def ShapeConstr (nnat : Nat) := Fin nnat → Option Nat

inductive ShapeIsType : List Nat → ShapeConstr nnat → List (SNat nnat) → Prop
  | nil {sc} : ShapeIsType [] sc []
  | cons_const {sc tl tl' hd n} :
      hd = n
      → ShapeIsType tl sc tl'
      → ShapeIsType (hd :: tl) sc (.const n :: tl')
  | cons_param {sc tl tl' hd idx} :
      (sc idx = .none ∨ sc idx = .some hd)
      → ShapeIsType tl sc tl'
      → ShapeIsType (hd :: tl) (Function.update sc idx (.some hd)) (.param idx :: tl')

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

end KLR.NKI
