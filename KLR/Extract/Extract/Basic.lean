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

We have a case for prop, which we use as a place holder for any types in Prop
when scanning the Lean definitions. We could just skip the Prop types, but it
may be useful to know that the type contains props at some point. Extractors
can ignore these if they choose, or represent them with a unit type.

There is a special case for enum, which is just a constant where we know the
type is an inductive where none of the constructors have any arguments. This
property is only known after we collect the whole type, so there is a
post-processing step which rewrites const to enum in those cases.
-/

inductive SimpleType where
  | bool | nat | int | float | string | prop
  | const (name : Name)
  | enum (name : Name)
  | option (elementType : SimpleType)
  | list (elementType : SimpleType)
  | pair (left right : SimpleType)
  deriving Repr, BEq

namespace SimpleType

-- Usually we want to handle common types separately.
-- For instance, placing them in a common, shared file.
def isCommon : SimpleType -> Bool
  | .bool | .nat | .int | .float | .string | .prop => true
  | .const .. | .enum .. => false
  | .option t | .list t => t.isCommon
  | .pair l r => l.isCommon && r.isCommon

-- Create a name for a simple type.
-- For example, List Nat becomes Nat.List. We reverse the names so there
-- is no chance of confusion with the Lean types.
def name : SimpleType -> Name
  | .bool => `Bool
  | .nat => `Nat
  | .int => `Int
  | .float => `Float
  | .string => `String
  | .prop => `Prop
  | .const name
  | .enum name => name
  | .option t => .str t.name "Option"
  | .list t => .str t.name "List"
  | .pair l r => .str (l.name ++ r.name) "Pair"

-- For languages like C we need to generate unique types for
-- each instance of list and option. Ths function collects all of
-- the additional types that need to be synthesized
def containers : SimpleType -> List SimpleType
  | .list t => .list t :: t.containers
  | .option t => .option t :: t.containers
  | .pair l r => .pair l r :: l.containers ++ r.containers
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
  | .pair l r => .pair (rewrite l) (rewrite r)
  | t => t

-- return the Names of container types
def containers : LeanType -> List SimpleType
  | .simple t => t.containers
  | .prod _ fs => fs.flatMap fun f => f.type.containers
  | .sum _ ts => ts.flatMap fun t => t.containers

end LeanType

private def collectType : Expr -> MetaM SimpleType
  | .const `Bool [] => return .bool
  | .const `Nat [] => return .nat
  | .const `UInt32 [] => return .nat
  | .const `Int [] => return .int
  | .const `Int32 [] => return .int
  | .const `Float [] => return .float
  | .const `Float32 [] => return .float
  | .const `String [] => return .string
  | .const n [] => return .const n
  | .app (.const `List [0]) t => return .list (<- collectType t)
  | .app (.const `Option [0]) t => return .option (<- collectType t)
  | .app (.app (.const `Prod [0,0]) l) r => return .pair (<- collectType l) (<- collectType r)
  | e => do
    match <- inferType e with
    | .sort .zero => return .prop
    | t => throwError s!"Unsupported Lean Type {repr e} : {repr t}"

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
