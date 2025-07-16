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
  deriving Repr, BEq

namespace SimpleType

-- Usually we want to handle common types separately.
-- For instance, placing them in a common, shared file.
def isCommon : SimpleType -> Bool
  | .bool | .nat | .int | .float | .string => true
  | .const .. | .enum .. => false
  | .option t | .list t => t.isCommon

-- For languages like C, we use, e.g. Bool_List instead of List Bool
def name : SimpleType -> Name
  | .bool => `Bool
  | .nat => `Nat
  | .int => `Int
  | .float => `Float
  | .string => `String
  | .const name
  | .enum name => name
  | .option t => .str t.name "Option"
  | .list t => .str t.name "List"

-- For languages like C we need to generate unique types for
-- each instance of list and option. Ths function collects all of
-- the additional types that need to be synthesized
def containers : SimpleType -> List SimpleType
  | .list t => .list t :: t.containers
  | .option t => .option t :: t.containers
  | _ => []

end SimpleType

structure Field where
  name : Name
  type : SimpleType
  deriving Repr

inductive LeanType where
  | simple (ty : SimpleType)
  | prod (name : Name) (fields : List Field)
  | sum (name : Name) (variants : List LeanType)
  deriving Repr

namespace LeanType

def name : LeanType -> Name
  | simple t => t.name
  | prod n ..
  | sum n .. => n

def singleton : LeanType -> Bool
  | simple .. => false
  | prod _ [] => true
  | prod .. => false
  | sum .. => false

def isEnum : LeanType -> Bool
  | simple .. => false
  | prod .. => false
  | sum _ vs => vs.all fun t => t.singleton

def rewriteEnums (enums : List Name) : LeanType -> LeanType
  | simple t => .simple (rewrite t)
  | prod n t => .prod n (t.map fun f => ⟨ f.name, rewrite f.type ⟩)
  | sum n vs => .sum n (vs.map (rewriteEnums enums))
where
  rewrite : SimpleType -> SimpleType
  | .const n => if enums.contains n then .enum n else .const n
  | .option t => .option (rewrite t)
  | .list t => .list (rewrite t)
  | t => t

-- return the Names of container types
def containers : LeanType -> List SimpleType
  | .simple .. => []
  | .prod _ fs => fs.flatMap fun f => f.type.containers
  | .sum _ ts => ts.flatMap fun t => t.containers

end LeanType

private def collectType [Monad m] [MonadError m] : Expr -> m SimpleType
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

def collectContainerTypes (l : List LeanType) : List SimpleType :=
  (l.flatMap fun t => t.containers).eraseDups

def collectTypes (names : List Name) : MetaM (List LeanType) := do
  let ty <- collectLeanTypes names
  let cty := collectContainerTypes ty
  let cty := cty.filter fun t => not t.isCommon
  return ty ++ cty.map .simple
