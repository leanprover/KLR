/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Core.Basic

/-
# Instances of ToJson for KLR

The instances are placed here, in a separate module, because we need to
manually write/replace some of the instances, and this may interfere with other
code.
-/

namespace KLR.Core
open Lean (FromJson ToJson)

/-
The tools we are interacting use a different encoding of infinity and NaN from
the default instance in Lean.
-/

instance : ToJson Float where
  toJson f :=
    match Lean.JsonNumber.fromFloat? f with
    | .inr n => .num n
    | .inl "NaN" => .str "nan"
    | .inl "Infinity" => .str "inf"
    | .inl "-Infinity" => .str "-inf"
    | _ => panic "internal error"

instance : FromJson Float where
  fromJson?
    | .str "inf" => return (1.0 / 0.0)
    | .str "-inf" => return (-1.0 / 0.0)
    | .str "nan" => return (0.0 / 0.0)
    | .num jn => return jn.toFloat
    | _ => throw "Expected a number or 'inf, '-inf, 'nan."

instance : ToJson Engine where
  toJson
  | .unassigned => .str "Unassigned"
  | .pool => .str "Pool"
  | .act => .str "Activation"
  | .pe => .str "PE"
  | .dma => .str "DMA"
  | .dve => .str "DVE"
  | .sp => .str "SP"

instance : FromJson Engine where
  fromJson?
  | .str "Unassigned" => return .unassigned
  | .str "Pool" => return .pool
  | .str "Activation" => return .act
  | .str "PE" => return .pe
  | .str "DMA" => return .dma
  | .str "DVE" => return .dve
  | .str "SP" => return .sp
  | .str s => throw s!"unknown engine type {s}"
  | _ => throw "expecting engine type"

deriving instance ToJson for Dtype
deriving instance ToJson for AluOp
deriving instance ToJson for Memory
deriving instance ToJson for TensorName
deriving instance ToJson for Const
deriving instance ToJson for IndexExpr
deriving instance ToJson for Index

deriving instance FromJson for Dtype
deriving instance FromJson for AluOp
deriving instance FromJson for Memory
deriving instance FromJson for TensorName
deriving instance FromJson for Const
deriving instance FromJson for IndexExpr
deriving instance FromJson for Index

deriving instance ToJson for TensorScalar
deriving instance ToJson for Operator
deriving instance ToJson for Expr
deriving instance ToJson for Stmt
deriving instance ToJson for Kernel

deriving instance FromJson for TensorScalar
deriving instance FromJson for Operator
deriving instance FromJson for Expr
deriving instance FromJson for Stmt
deriving instance FromJson for Kernel
