/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import KLR.Core
import KLR.File
import KLR.NKI.Basic
import KLR.Python
import KLR.Serde
import Lean

/-
Output functions for C++

Note: not too worried about formatting; will run clang-format on result.
-/
namespace Extract.Cpp
open Lean Meta

def varName : Name -> String
  | .str _ s => renameVar s
  | _ => panic! "bad name"
where
  renameVar : String -> String
  | "Bool" | "bool" => "boolean"
  | "Int" | "int" => "int32"
  | "Float" | "float" => "float32"
  | "String" | "string" => "str"
  | "Const" | "const" => "constant"
  | "register" => "reg"
  | s => s

private def enumName (name : Name) : String := varName name

private def cppName (name : Name) : String :=
  match name with
  | .str n s@⟨c :: _⟩ =>
    let s := s.replace "'" "_"
    if c.isUpper then s else
    match cppName n with
    | "" => s 
    | s1 => s1 ++ "_" ++ s
  | .anonymous => ""
  | _ => panic! s!"invalid CPP name {name}"

instance : ToString Name where toString n := cppName n

-- Construct C type for a SimpleType.
-- Note, in C we don't need separate option types: we use NULL (or zero).
def genType (t : SimpleType) : String :=
  match t with
  | .bool => "bool"
  | .nat => "Nat"
  | .int => "Int"
  | .float => "Float"
  | .string => "String"
  | .prop => "Prop"
  | .const `Lean.Name => "String"
  | .const `KLR.Core.Reg => "Nat"
  | .const name => s!"Ptr<{name}>"
  | .enum name => s!"{name}"
  | .option t => genType t
  | .list t => s!"List<{t.name}>"
  | .pair .. => panic! "TODO"

private def genStruct (name : Name) (fields : List Field) : IO Unit := do
  IO.println s!"struct {name} final \{"
  fields.forM fun f => do
    let ty := genType f.type
    IO.println s!"  {ty} {f.name};"
  IO.println "};"

private def genEnum (name : Name) (variants : List LeanType) : IO Unit := do
  IO.println s!"enum class {name} \{"
  match variants with
  | [] => pure ()
  | v :: rest => do
    IO.println s!"{enumName v.name} = 1,"
    for v in rest do
      IO.println s!"{enumName v.name},"
    IO.println "};"

private def genUnion (name : Name) (variants : List LeanType) : MetaM Unit := do
  let tagName := Name.str name "Tag"
  IO.println s!"struct {name} \{"
  genEnum tagName variants
  for t in variants do
    match t with
    | .simple .. => pure ()
    --| .prod _ [] => pure ()
    | .prod n fs => genStruct n fs
    | .sum .. => throwError "unexpected union nesting"
  IO.println "union U {"
  IO.println "  U() {}"
  IO.println "  ~U() {}"
  for t in variants do
    match t with
    | .simple t => IO.println s!"{t.name} {varName t.name};"
    --| .prod _ [] => pure ()
    | .prod n .. => IO.println s!"{n} {varName n};"
    | .sum .. => throwError "unexpected union nesting"
  IO.println "};"
  IO.println s!"enum {tagName} tag;"
  IO.println s!"union U u;"
  IO.println s!"~{name}() \{"
  IO.println "  switch (tag) {"
  for t in variants do
    IO.println s!" case Tag::{enumName t.name}:"
    IO.println s!"   u.{varName t.name}.~{t.name}(); break;"
  IO.println "}}};"

private def genList (ty : SimpleType) := do
  let name := ty.list.name
  let vname := Name.mkStr1 (varName ty.name).toLower
  let fs : List Field := [ ⟨`next, ty.list⟩, ⟨vname, ty⟩ ]
  genStruct name fs

def genCppType (ty : LeanType) : MetaM Unit := do
  IO.println ""
  match ty with
  --| .simple (.list t) => genList t
  | .simple _ => pure ()
  | .prod name fields => genStruct name fields
  | .sum name variants =>
    if ty.isEnum
    then genEnum name variants
    else genUnion name variants

def commonAST : MetaM (List LeanType) := do
  let atomic := [.bool, .nat, .int, .float, .string]
  let lists := atomic.map fun t => .simple (.list t)
  let options := atomic.map fun t => .simple (.option t)
  let tys <- collectLeanTypes [ `KLR.Core.Pos ]
  return lists ++ options ++ tys

def fileAST : MetaM (List LeanType) := do
  let tys <- collectLeanTypes [
    `KLR.Serde.KLRFile,
    `KLR.Serde.KLRMetaData,
    `KLR.File.Contents
  ]
  return tys


def pythonAST: MetaM (List LeanType) := do
  collectTypes [
    `KLR.Python.Const,
    `KLR.Python.Ctx,
    `KLR.Python.BoolOp,
    `KLR.Python.CmpOp,
    `KLR.Python.UnaryOp,
    `KLR.Python.BinOp,
    `KLR.Python.Expr',
    `KLR.Python.Expr,
    `KLR.Python.Keyword,
    `KLR.Python.Stmt',
    `KLR.Python.Stmt,
    `KLR.Python.Args,
    `KLR.Python.Fun,
    `KLR.Python.Kernel,
   ]

def nkiAST : MetaM (List LeanType) := do
  collectTypes [
    `KLR.NKI.Value,
    `KLR.NKI.BinOp,
    `KLR.NKI.Expr',
    `KLR.NKI.Expr,
    `KLR.NKI.Index,
    `KLR.NKI.Keyword,
    `KLR.NKI.Pattern,
    `KLR.NKI.Stmt',
    `KLR.NKI.Stmt,
    `KLR.NKI.Param,
    `KLR.NKI.Fun,
    `KLR.NKI.Arg,
    `KLR.NKI.Kernel,
  ]

def klrAST: MetaM (List LeanType) := do
  collectTypes [
    -- Core.Tensor
    `KLR.Core.Memory,
    `KLR.Core.Dtype,
    `KLR.Core.Shape,
    `KLR.Core.Address,
    `KLR.Core.TensorSram,
    `KLR.Core.Slice,
    `KLR.Core.Index,
    `KLR.Core.AccessBasic,
    `KLR.Core.APPair,
    `KLR.Core.AccessPattern,
    `KLR.Core.Access,
    `KLR.Core.TensorHbm,
    `KLR.Core.ParQuadrant,
    `KLR.Core.TensorView,
    `KLR.Core.TensorRef,
    `KLR.Core.TensorArg,
    -- Core.Operators (Parameters)
    `KLR.Core.Engine,
    `KLR.Core.Immediate,
    `KLR.Core.ActivationImm,
    `KLR.Core.DataPattern,
    `KLR.Core.AluOp,
    `KLR.Core.DropoutThresholdType,
    `KLR.Core.AccumCmd,
    `KLR.Core.ActivationFunc,
    `KLR.Core.AffineSelectCmp,
    `KLR.Core.DgeComputeOp,
    `KLR.Core.DmaBounds,
    `KLR.Core.MatmulGroupElement,
    `KLR.Core.IndexMissBehavior,
    `KLR.Core.TensorScalarReverseOps,
    `KLR.Core.TensorSubDim,
    -- Core.Operators (Instructions)
    `KLR.Core.Dropout,
    `KLR.Core.Activate,
    `KLR.Core.AffineSelect,
    `KLR.Core.DmaCopy,
    `KLR.Core.DmaTranspose,
    `KLR.Core.Transpose,
    `KLR.Core.LoadMaskRegister,
    `KLR.Core.Shuffle,
    `KLR.Core.MemSet,
    `KLR.Core.Iota,
    `KLR.Core.LoadStationary,
    `KLR.Core.MatMul,
    `KLR.Core.LocalGather,
    `KLR.Core.RangeSelect,
    `KLR.Core.ScalarTensorTensor,
    `KLR.Core.CopyPredicated,
    `KLR.Core.TensorTensorScan,
    `KLR.Core.MatchValueLoad,
    `KLR.Core.FindIndex8,
    `KLR.Core.MatchReplace8,
    `KLR.Core.Max8,
    `KLR.Core.BatchNormAggregate,
    `KLR.Core.BatchNormStats,
    `KLR.Core.Reciprocal,
    `KLR.Core.Copy,
    `KLR.Core.TensorReduce,
    `KLR.Core.Operator,
    -- Core.Basic
    `KLR.Core.Value,
    `KLR.Core.Keyword,
    `KLR.Core.Expr,
    `KLR.Core.Stmt,
    `KLR.Core.Kernel,
   ]

private def header (isH : Bool) (includes : List String := []) : String :=
  let inc := includes.map fun file => s!"#include \"{file}\""
  let inc := String.intercalate "\n" inc
s!"/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Written by the KLR Contributors (https://github.com/leanprover/KLR)
*/
{if isH then "#pragma once\n" else ""}
// This file is automatically generated from KLR.
// Manual edits to this file will be overwritten.

#include \"klir_common.hpp\"
{inc}

namespace klr \{
"

def headerH (includes : List String := []) : String := header (isH := true) includes
def headerC (includes : List String := []) : String := header (isH := false) includes

private def genTypes (tys : List LeanType) : MetaM Unit :=
  for ty in tys do
    genCppType ty

def generateKlrAST : MetaM Unit := do
  IO.println (headerH [])
  IO.println "// KLR.Core Abstract Syntax"
  genTypes (<- commonAST)
  genTypes (<- klrAST)
  IO.println "struct Python_Kernel {};"
  IO.println "struct NKI_Kernel {};"
  genTypes (<- fileAST)
  IO.println "}"

run_meta generateKlrAST
