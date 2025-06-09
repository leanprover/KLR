/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import KLR.NKI.Basic
import KLR.Python
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
  | "bool" => "b"
  | "int" => "i"
  | "float" => "f"
  | "string" => "s"
  | "const" => "c"
  | s => s

private def CName (name : Name) : String :=
  match name with
  | .str n s => preFix "" n ++ s.replace "'" "_"
  | _ => panic! "bad name"
where
  preFix (acc : String) : Name -> String
  | .str .anonymous "KLR" => acc
  | .str n s => preFix (dropUnder s ++ "_" ++ acc) n
  | .anonymous => ""
  | .num _ _ => panic! "numeric name"
  dropUnder (s : String) : String :=
  if s.endsWith "_" || s.endsWith "'" then s.dropRight 1 else s

instance : ToString Name where toString n := CName n

private def genType (t : SimpleType) : String :=
  match t with
  | .bool => "bool"
  | .nat => "u32"
  | .int => "i32"
  | .float => "f32"
  | .string => "const char*"
  | .const name => s!"struct {name}*"
  | .enum name => s!"enum {name}"
  | .option (.enum n) => genType (.enum n) ++ "*"
  | .option t => genType t
  | .list .bool => "struct Bool_List*"
  | .list .nat => "struct Nat_List*"
  | .list .int => "struct Int_List*"
  | .list .float => "struct Float_List*"
  | .list .string => "struct String_List*"
  | .list (.const n)
  | .list (.enum n) => s!"struct {n}_List*"
  | .list _ => panic! "unsupported list type"

private def genStruct (name : Name)
                      (fields : List Field)
                      (var : String := "")
                      : MetaM Unit := do
  IO.println s!"struct {name} \{"
  fields.forM fun f => do
    let ty := genType f.type
    IO.println s!"  {ty} {f.name};"
  IO.println s!"} {var};"

private def genEnum' (name : Name)
                     (variants : List LeanType)
                     (var : String := "")
                     : MetaM Unit := do
  let names := variants.map fun v => CName v.name
  let rhs := String.intercalate ", " names
  IO.println s!"enum {name} \{ {rhs} } {var};"
  return ()

private def genEnum : LeanType -> MetaM Unit
  | .sum name variants => genEnum' name variants ""
  | _ => throwError "Cannot gen enum for product"

private def genUnion (name : Name) (variants : List LeanType) : MetaM Unit := do
  IO.println s!"struct {name} \{"
  genEnum' (.str name "Tag") variants "tag"
  IO.println "union {"
  variants.forM fun t => do
    match t with
    | .prod _ [] => pure ()
    | .prod n fs => genStruct n fs (varName n)
    | .sum .. => pure ()
  IO.println "};"
  IO.println "};"

def genCType (ty : LeanType) : MetaM Unit := do
  IO.println ""
  match ty with
  | .prod name fields => genStruct name fields
  | .sum name variants =>
    if ty.isEnum
    then genEnum (.sum name variants)
    else genUnion name variants

def genInitBody (retTy : Name) (t : LeanType) : MetaM Unit := do
  match t with
  | .prod name fields => do
    let ptr := genType (.const retTy)
    let element1 := (varName retTy).toLower
    let element2 := varName name
    IO.println "{"
    IO.println s!"  {ptr} res = region_alloc(region, sizeof(*res));"
    IO.println "  if (!res) return NULL;"
    IO.println s!"  res->{element1}->tag = {name};"
    for f in fields do
      IO.println s!"  res->{element1}->{element2}.{f.name} = {f.name};"
    IO.println "  return res;"
    IO.println "}"
  | _ => throwError "internal error"

def genMkFuns (retTy : Name) (t : LeanType) : MetaM Unit := do
  match t with
  | .prod name fields => do
    let fnName := "mk" ++ (toString name).capitalize
    let ptr := genType (.const retTy)
    let args := fields.map fun f => genType f.type ++" "++ f.name.toString
    let args := String.intercalate ", " args
    let args := if args != "" then args ++ "," else args
    IO.println ""
    IO.println s!"static inline {ptr}"
    IO.println s!"{fnName}({args} struct region *region)"
    genInitBody retTy t
  | .sum _ variants =>
    for v in variants do
      genMkFuns retTy v

def pythonAST: MetaM (List LeanType) := do
  collectLeanTypes [
    `KLR.Python.Pos,
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
  collectLeanTypes [
    `KLR.NKI.Pos,
    `KLR.NKI.Value,
    `KLR.NKI.BinOp,
    `KLR.NKI.Expr',
    `KLR.NKI.Expr,
    `KLR.NKI.Index,
    `KLR.NKI.Keyword,
    `KLR.NKI.Stmt',
    `KLR.NKI.Stmt,
    `KLR.NKI.Param,
    `KLR.NKI.Fun,
    `KLR.NKI.Arg,
    `KLR.NKI.Kernel,
  ]

def header :=
"// This file is automatically generated from KLR.
// Manual edits to this file will be overwritten.
#include \"stdc.h\"
#include \"region.h\"
"

private def genList (name : Name) (ty : SimpleType) := do
  IO.println ""
  IO.println s!"struct {name}_List \{"
  IO.println s!"  struct {name}_List *next;"
  IO.println s!"  {genType ty} {String.toLower (varName name)};"
  IO.println "};"

private def genTypes (tys : List LeanType) : MetaM Unit :=
  for ty in tys do
    genCType ty

private def genAlloc (tys : List LeanType) (retTy name : Name) : MetaM Unit := do
  match tys.find? (fun t => t.name == name) with
  | none => throwError s!"Type {name} not found"
  | some t => genMkFuns retTy t

def generatePythonAST : MetaM Unit := do
  let tys <- pythonAST
  IO.println header
  IO.println "// KLR.Python Abstract Syntax"
  genTypes tys
  genList `KLR.Python.CmpOp (.enum `KLR.Python.CmpOp)
  genList `String .string
  for n in ["Expr", "Keyword", "Stmt", "Fun"] do
    let n := .str `KLR.Python n
    genList n (.const n)
  genAlloc tys `KLR.Python.Expr `KLR.Python.Expr'
  genAlloc tys `KLR.Python.Stmt `KLR.Python.Stmt'

def generateNkiAST : MetaM Unit := do
  let tys <- nkiAST
  IO.println header
  IO.println "// KLR.NKI Abstract Syntax"
  genTypes tys
  genList `String .string
  for n in ["Expr", "Index", "Keyword", "Stmt", "Fun"] do
    let n := .str `KLR.NKI n
    genList n (.const n)
  genAlloc tys `KLR.NKI.Expr `KLR.NKI.Expr'
  genAlloc tys `KLR.NKI.Stmt `KLR.NKI.Stmt'
