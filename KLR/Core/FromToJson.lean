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
open Lean (JsonNumber Json FromJson fromJson? ToJson toJson)

/-
The tools we are interacting use a different encoding of infinity and NaN from
the default instance in Lean.
-/

instance : ToJson Float where
  toJson f :=
    match JsonNumber.fromFloat? f with
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

instance : ToJson Memory where
  toJson
  | .hbm => "dram"
  | .sbuf => "sbuf"
  | .pmem => "pmem"
  | .reg => "reg"

instance : FromJson Memory where
  fromJson?
  | .str "dram" => return .hbm
  | .str "sbuf" => return .sbuf
  | .str "pmem" => return .pmem
  | .str "reg" => return .reg
  | _ => throw "expecting memory type"

deriving instance ToJson for Dtype
deriving instance ToJson for AluOp
deriving instance ToJson for Shape
deriving instance ToJson for Address

instance : ToJson TensorName where
  toJson t := .mkObj [
    ("name", toJson t.name),
    ("dtype", toJson t.dtype),
    ("shape", toJson t.shape),
    ("address", toJson t.address)
  ]

instance toJsonInst : ToJson Slice where
  toJson s := toJson (s.l, s.u, s.step)

instance fromJsonInst : FromJson Slice where
  fromJson? j := do
    let (l, u, step) <- fromJson? j
    Slice.make l u step

#guard
  let s := Slice.make! 1 5 1
  get! (fromJsonInst.fromJson? (toJsonInst.toJson s)) == s

deriving instance ToJson for Index

instance : ToJson AccessBasic where
  toJson acc := .mkObj [
    ("tensor", toJson acc.tensor),
    ("indexes", toJson acc.indexes)
  ]

deriving instance ToJson for APPair
deriving instance ToJson for AccessPattern
deriving instance ToJson for Access

deriving instance FromJson for Dtype
deriving instance FromJson for AluOp
deriving instance FromJson for Shape
deriving instance FromJson for Address

private def getField [FromJson t] (j : Json) (name : String) : Err t := do
  fromJson? (<- j.getObjVal? name)

instance : FromJson TensorName where
  fromJson? j := do
    TensorName.make (<- getField j "name")
                    (<- getField j "dtype")
                    (<- getField j "shape")
                    (some (<- getField j "address"))

deriving instance FromJson for Index

instance : FromJson AccessBasic where
  fromJson? j := do
    AccessBasic.make (<- getField j "tensor")
                     (<- getField j "indexes")

deriving instance FromJson for APPair
deriving instance FromJson for AccessPattern
deriving instance FromJson for Access

deriving instance ToJson for TensorScalar
deriving instance ToJson for Operator
deriving instance ToJson for Value
deriving instance ToJson for Expr
deriving instance ToJson for Stmt
deriving instance ToJson for Kernel

deriving instance FromJson for TensorScalar
deriving instance FromJson for Operator
deriving instance FromJson for Value
deriving instance FromJson for Expr
deriving instance FromJson for Stmt
deriving instance FromJson for Kernel
