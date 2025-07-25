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

import Extract.Basic
import KLR.Core
import KLR.File
import KLR.NKI.Basic
import KLR.Python
import KLR.Serde
import Lean

/-
Output functions for C

Note: not too worried about formatting; will run clang-format on result.
-/
namespace Extract.C
open Lean Meta

def varName : Name -> String
  | .str _ s => renameVar s
  | _ => panic! "bad name"
where
  renameVar : String -> String
  | "Bool" | "bool" => "b"
  | "Int" | "int" => "i"
  | "Float" | "float" => "f"
  | "String" | "string" => "s"
  | "Const" | "const" => "c"
  | "register" => "r"
  | s => s

private def cName (name : Name) : String :=
  match name with
  | .str n s => preFix "" n ++ s.replace "'" "_"
  | .anonymous => ""
  | .num n _ => preFix "" n
where
  preFix (acc : String) : Name -> String
    | .str .anonymous "KLR" => acc
    | .str n s => preFix (dropUnder s ++ "_" ++ acc) n
    | .anonymous => acc
    | .num n _ => preFix acc n
  dropUnder (s : String) : String :=
    if s.endsWith "_" || s.endsWith "'" then s.dropRight 1 else s

instance : ToString Name where toString n := cName n

-- Construct C type for a SimpleType.
-- Note, in C we don't need separate option types: we use NULL (or zero).
def genType (t : SimpleType) : String :=
  match t with
  | .bool => "bool"
  | .nat => "u32"
  | .int => "i32"
  | .float => "f32"
  | .string => "char*"
  | .prop => "struct Prop"
  | .const `Lean.Name => "char*"
  | .const `KLR.Core.Reg => "u32"
  | .const name => s!"struct {name}*"
  | .enum name => s!"enum {name}"
  | .option t => genType t
  | .list _ => s!"struct {t.name}*"
  | .pair .. => panic! "TODO"

private def genStruct (name : Name) (fields : List Field) : IO Unit := do
  IO.println s!"struct {name} \{"
  fields.forM fun f => do
    let ty := genType f.type
    IO.println s!"  {ty} {f.name};"
  IO.println "};"

private def genEnum (name : Name) (variants : List LeanType) : IO Unit := do
  IO.println s!"enum {name} \{"
  match variants with
  | [] => pure ()
  | v :: rest => do
    IO.println s!"{v.name} = 1,"
    for v in rest do
      IO.println s!"{v.name},"
    IO.println "};"

private def genUnion (name : Name) (variants : List LeanType) : MetaM Unit := do
  let tagName := Name.str name "Tag"
  genEnum tagName variants
  for t in variants do
    match t with
    | .simple .. => pure ()
    | .prod _ [] => pure ()
    | .prod n fs => genStruct n fs
    | .sum .. => throwError "unexpected union nesting"
  IO.println s!"struct {name} \{"
  IO.println s!"enum {tagName} tag;"
  IO.println "union {"
  for t in variants do
    match t with
    | .simple t => IO.println s!"{t.name} {varName t.name};"
    | .prod _ [] => pure ()
    | .prod n .. => IO.println s!"struct {n} {varName n};"
    | .sum .. => throwError "unexpected union nesting"
  IO.println "};"
  IO.println "};"

private def genList (ty : SimpleType) := do
  let name := ty.list.name
  let vname := Name.mkStr1 (varName ty.name).toLower
  let fs : List Field := [ ⟨`next, ty.list⟩, ⟨vname, ty⟩ ]
  genStruct name fs

def genCType (ty : LeanType) : MetaM Unit := do
  IO.println ""
  match ty with
  | .simple (.list t) => genList t
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
    `KLR.Core.TensorName,
    `KLR.Core.Slice,
    `KLR.Core.Index,
    `KLR.Core.AccessBasic,
    `KLR.Core.APPair,
    `KLR.Core.AccessPattern,
    `KLR.Core.Access,
    `KLR.Core.TensorHbm,
    `KLR.Core.ParQuadrant,
    `KLR.Core.TensorSram,
    `KLR.Core.TensorRef,
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
    `KLR.Core.TensorScalar,
    `KLR.Core.TensorTensor,
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
Authors: Paul Govereau, Sean McLaughlin
*/
{if isH then "#pragma once\n" else ""}
// This file is automatically generated from KLR.
// Manual edits to this file will be overwritten.

#include \"stdc.h\"
#include \"region.h\"
{inc}
"

def headerH (includes : List String := []) : String := header (isH := true) includes
def headerC (includes : List String := []) : String := header (isH := false) includes

private def genTypes (tys : MetaM (List LeanType)) : MetaM Unit :=
  for ty in <- tys do
    genCType ty

def generateCommonAST: MetaM Unit := do
  IO.println headerH
  IO.println "// KLR Common Abstract Syntax"
  genTypes commonAST

def generateFileAST: MetaM Unit := do
  IO.println (headerH ["ast_common.h", "ast_python_core.h", "ast_nki.h", "ast_klir.h"])
  IO.println "// KLR File Formats"
  genTypes fileAST

def generatePythonAST : MetaM Unit := do
  IO.println (headerH ["ast_common.h"])
  IO.println "// KLR.Python Abstract Syntax"
  genTypes pythonAST

def generateNkiAST : MetaM Unit := do
  IO.println (headerH ["ast_common.h"])
  IO.println "// KLR.NKI Abstract Syntax"
  genTypes nkiAST

def generateKlrAST : MetaM Unit := do
  IO.println (headerH ["ast_common.h"])
  IO.println "// KLR.Core Abstract Syntax"
  genTypes klrAST
