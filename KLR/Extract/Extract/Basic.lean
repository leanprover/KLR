/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean

/-
Collect information about Lean types that will be used to generate C and Python files.
Note: this library is only used at compile-time.
-/

namespace Extract
open Lean Meta

/-
The types below are a simplified representation of Lean structures and
inductives that can be used for generating C++ and Python code.
-/

inductive SimpleType where
  | bool | nat | int | float | string
  | const (name : Name)
  | enum (name : Name)
  | option (elementType : SimpleType)
  | list (elementType : SimpleType)
  deriving Repr

structure Field where
  name : Name
  type : SimpleType
  deriving Repr

inductive LeanType where
  | prod (name : Name) (fields : List Field)
  | sum (name : Name) (variants : List LeanType)
  deriving Repr

namespace LeanType

def name : LeanType -> Name
  | prod n _ | sum n _ => n

def singleton : LeanType -> Bool
  | prod _ [] => true | _ => false

def isEnum : LeanType -> Bool
  | prod .. => false
  | sum _ vs => vs.all fun t => t.singleton

def rewriteEnums (enums : List Name) : LeanType -> LeanType
  | prod n t => .prod n (t.map fun f => ⟨ f.name, rewrite f.type ⟩)
  | sum n vs => .sum n (vs.map (rewriteEnums enums))
where
  rewrite : SimpleType -> SimpleType
  | .const n => if enums.contains n then .enum n else .const n
  | .option t => .option (rewrite t)
  | .list t => .list (rewrite t)
  | t => t

end LeanType

private def collectType : Expr -> MetaM SimpleType
  | .const `Bool [] => return .bool
  | .const `Nat [] => return .nat
  | .const `Int [] => return .int
  | .const `Float [] => return .float
  | .const `String [] => return .string
  | .const n [] => return .const n
  | .app (.const `List [0]) t => return .list (<- collectType t)
  | .app (.const `Option [0]) t => return .option (<- collectType t)
  | e => throwError s!"Unsupported Lean Type {e}"

private def collectBody (ci : ConstructorVal) : MetaM (List Field) :=
  forallTelescopeReducing ci.type fun xs _ => do
    let mut fields := []
    for i in [:ci.numFields] do
      let ld <- xs[ci.numParams + i]!.fvarId!.getDecl
      let ty <- collectType ld.type
      fields := ⟨ ld.userName, ty ⟩ :: fields
    return fields.reverse

private def collectStructure (name : Name) : MetaM LeanType := do
  let tci <- getConstInfoInduct name
  let ci <- getConstInfoCtor tci.ctors[0]!
  return .prod name (<- collectBody ci)

private def collectConstructor (name : Name) : MetaM LeanType := do
  let ci <- getConstInfoCtor name
  return .prod ci.name (<- collectBody ci)

private def collectInductive (name : Name) : MetaM LeanType := do
  let tci <- getConstInfoInduct name
  let mut variants := []
  for c in tci.ctors do
    let variant <- collectConstructor c
    variants := variant :: variants
  return .sum name variants.reverse

def collectLeanType (name : Name) : MetaM LeanType := do
  match getStructureInfo? (<- getEnv) name with
  | some _ => collectStructure name
  | none => collectInductive name

def showLeanType (name : Name) : MetaM Unit := do
  let t <- collectLeanType name
  IO.println (reprStr t)

-- Note: we want the list to remain in given order
def collectLeanTypes (names : List Name) : MetaM (List LeanType) := do
  let mut enums := []
  let mut res := []
  for name in names do
    let ty <- collectLeanType name
    if ty.isEnum then
      enums := name :: enums
    res := ty :: res
  return res.reverse.map fun t => t.rewriteEnums enums
