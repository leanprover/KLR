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

import KLR.Compile.Pass
import KLR.NKI.Basic
import KLR.NKI.Pretty
import KLR.Util

/-
Process class definitions

This pass does two things: move class methods to the function list, and
generate constructor and initializer functions.
-/

namespace KLR.NKI
open Compile.Pass

abbrev Cls := Pass Unit

/-
Generate a constructor function based on the init function.

If the init function has the signature

  def __init__(x,y,z=1)

Then the constructor will have the form:

  def C(x,y,z=1):
    self = builtin.new("C")
    self.__init__(x,y,z)
    return self

This function will be registered under the class name, so expressions
like `x = C(...)`, will end up calling this generated function.

Note, regular projections from the class, like `C.x`m will also work since we
move all of these to the environment.
-/
private def genNew (c : Class) (init : Fun) : Cls Fun := do
  let name := c.name
  let pos := { line := 0 : Pos }
  let var n : Expr := ⟨ .var n, pos ⟩
  let args := init.args.map fun p => var p.name.toName
  let body : List Stmt' := [
    .letM (.var `self) none ⟨.object name c.fields, pos ⟩,
    .expr ⟨.call (var init.name) args [], pos ⟩,
    .ret ⟨ .var `self, pos ⟩
    ]
  return {
    name := name
    file := s!"<{c.name} new>"
    body := body.map fun b => Stmt.mk b pos
    args := init.args.tail
  }

/-
Generate an init function.

If a class is declared with fields:

  class C:
    x : int
    y : int = 1

Then the default init function will have the form:

  def __init__(self, x=None, y=1):
   self.x = x
   self.y = y
   self.__post_init__()

This function should work for both dataclasses and for NamedTuple.
-/
private def genInitStandard (c : Class) : Cls Fun := do
  let pos := { line := 0 : Pos }
  let args := c.fields.map fun fld => Param.mk fld.name fld.expr
  let vars := c.fields.map fun fld => Expr.mk (.var fld.name.toName) pos
  let flds := c.fields.map fun fld => Expr.mk (.var (.str `self fld.name)) pos
  let sets := (flds.zip vars).map fun (f,v) => Stmt.mk (.setM f v false) pos
  let pifn := Expr.mk (.var (.str c.name "__post_init__")) pos
  let post := Expr.mk (.call pifn [⟨.var `self, pos⟩] []) pos
  let body := sets ++ [.mk (.expr post) pos]
  return {
    name := .str c.name "__init__"
    file := s!"<{c.name} init>"
    body := body
    args := .mk "self" none :: args
  }

private def genInitEnum (c : Class) : Cls Fun := do
  let pos := { line := 0 : Pos }
  let none := Expr.mk (.value .none) pos
  let fs : List Keyword := [.mk "name" none, .mk "value" none]
  genInitStandard { c with fields := fs }

private def isEnum (c : Class) : Bool :=
  c.bases.contains `Enum

private def genInit (c : Class) : Cls Fun := do
  if isEnum c then
    genInitEnum c
  else
    genInitStandard c

-- Generate an empty post_init function
private def genPostInit (c : Class) : Cls Fun :=
  return {
    name := .str c.name "__post_init__"
    file := s!"<{c.name} post_init>"
    args := [.mk "self" none]
  }

private def isInit (f : Fun) : Bool :=
  match f.name with
  | .str _ "__init__" => true
  | _ => false

private def isPostInit (f : Fun) : Bool :=
  match f.name with
  | .str _ "__post_init__" => true
  | _ => false

/-
Check for init and post_init functions, and if not found generate them.
Also generate the constructor function for the class.
-/
private def ensureInit (c : Class) : Cls (List Fun) := do
  let (init, fs) <- match c.methods.partition isInit with
    | ([], fs) => pure ((<- genInit c),fs)
    | ([f], fs) => pure (f, fs)
    | _ => throw "internal error: multiple init functions found"
  let fs <- match c.methods.find? isPostInit with
    | some _ => pure fs
    | none => pure ((<- genPostInit c) :: fs)
  return (<- genNew c init) :: init :: fs

/-
Generate init functions, and move all of the class methods to the global
function list. Also move all class fields to the global constants list.

If a class is defined as:

  class C:
    x = 1
    def f(): ...

Then register the globals:

  def C(x=1): ...
  def C.__init__(self, x=1): ...
  def C.__post_init__(self): ...
  C.x = 1
  def C.f(): ...

For an object of type C, `x.f(...)` is syntactic sugar for `C.f(x,...)`.
-/

private def qual (name : Name) (s : String) : String :=
  (Lean.Name.str name s).toString

def genClasses (k : Kernel) : Cls Kernel := do
  let mut vs := #[]
  let mut fs := #[]
  let mut cs := #[]
  for c in k.cls do
    let ms <- ensureInit c
    let vars := c.fields.map fun kw => Arg.mk (qual c.name kw.name) kw.expr
    fs := fs.append ms.toArray
    cs := cs.push { c with methods := [] }
    vs := vs.append vars.toArray

  -- Note: eraseDups removes the earlier elements in the list
  let k := { k with
    funs    := (k.funs ++ fs.toList).eraseDups
    cls     := cs.toList
    globals := (k.globals ++ vs.toList).eraseDups
  }
  dbg_trace s!"========\n{Std.format k}\n=========="
  return k
