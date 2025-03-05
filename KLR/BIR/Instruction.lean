/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Core

/-
Support types for automatically generated instructions

This file contains type definitions required by the automatically
generated code in Instructions.lean.

Note: the naming of fields is carefully designed so that the derived
instances of to- and from-json are compatible with the compiler.
-/
namespace KLR.BIR
export KLR.Core (Dtype Shape Engine AluOp Memory APPair)

-- TODO: this is incomplete
structure QAETerm where
  coeff: Int
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure QuasiAffineExpr where
  kind : String := "AffExprKind"
  --terms: List QAETerm := []
  --c : Int := 0
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

abbrev ShapeVector := List Nat
abbrev LoopAxis := String

inductive InstSyncType where
  | DataPathType
  | SequencerType
  | DMAType
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure PhysicalAccessPattern where
  ap : List (List Int)
  dtype : String
  offset : Nat
  memsetref : String
  memref : String
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure SymbolicAccessPattern where
  ap : List (List Int)
  dtype : String
  addrs : List QuasiAffineExpr
  access_shape : List Int
  memsetref : String
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure RegisterAccessPattern where
  ap : List (List Int)
  dtype : String
  memsetref : String
  reg_ap_offset : String
  regref : String
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure RegisterAccess where
  dtype : String
  regref : String
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure ImmValue where
  dtype : String
  value : Lean.JsonNumber
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure ImmArray where
  dtype : String
  value_array : List Lean.JsonNumber
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure Value where
  value : Lean.JsonNumber
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure SymbolicImmValue where
  dtype : String
  value_list : List Value
  expr : QuasiAffineExpr
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

inductive Argument where
  | PhysicalAccessPattern : PhysicalAccessPattern -> Argument
  | SymbolicAccessPattern : SymbolicAccessPattern -> Argument
  | RegisterAccessPattern : RegisterAccessPattern -> Argument
  | RegisterAccess : RegisterAccess -> Argument
  | ImmValue : ImmValue -> Argument
  | ImmArray : ImmArray -> Argument
  | SymbolicImmValue : SymbolicImmValue -> Argument
  deriving BEq, Repr

-- The default From- and ToJson place the inductive name outside
-- of the object containing the constructor arguments, we need it
-- on the inside.
def tagObj [Lean.ToJson a] (name tag : String) (x : a) : Lean.Json :=
  (Lean.toJson x).setObjVal! name (.str tag)

instance : Lean.ToJson Argument where
  toJson
    | .PhysicalAccessPattern ap => tagObj "kind" "physical_ap" ap
    | .SymbolicAccessPattern ap => tagObj "kind" "symbolic_ap" ap
    | .RegisterAccessPattern ap => tagObj "kind" "register_ap" ap
    | .RegisterAccess r => tagObj "kind" "register_access" r
    | .ImmValue v => tagObj "kind" "imm_value" v
    | .ImmArray v => tagObj "kind" "imm_array" v
    | .SymbolicImmValue v => tagObj "kind" "symbolic_imm_value" v

instance : Lean.FromJson Argument where
  fromJson? j := do
    let name <- j.getObjValAs? String "kind"
    match name with
    | "physical_ap" => return .PhysicalAccessPattern (<- Lean.fromJson? j)
    | "symbolic_ap" => return .SymbolicAccessPattern (<- Lean.fromJson? j)
    | "register_ap" => return .RegisterAccessPattern (<- Lean.fromJson? j)
    | "register_access" => return .RegisterAccess (<- Lean.fromJson? j)
    | "imm_value" => return .ImmValue (<- Lean.fromJson? j)
    | "imm_array" => return .ImmArray (<- Lean.fromJson? j)
    | "symbolic_imm_value" => return .SymbolicImmValue (<- Lean.fromJson? j)
    | _ => throw s!"Unknown argument kind {name}"

structure Instruction where
  name : String
  engine : Engine := .unassigned
  ins : List Argument := []
  outs : List Argument := []
  -- TODO: not using these right now...
  --dependencies : Option (List String) := none
  --unroll_dependencies : Option (List String) := none
  --loop_carried_dependencies : Option (List String) := none
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson
