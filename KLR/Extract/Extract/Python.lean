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
import Extract.C
import KLR.Python
import Lean

/-
Output functions for Python
-/

namespace Extract.Python
open Lean Meta

private def PyName (name : Name) (f : String -> String := id) : String :=
  match name with
  | .str _ s => f (s.replace "'" "_")
  | _ => panic! "found invalid name"

instance : ToString Name where toString n := PyName n

private def genType : SimpleType -> String
  | .bool => "bool"
  | .nat | .int => "int"
  | .float => "float"
  | .string => "str"
  | .prop => panic! "TODO"
  | .const name
  | .enum name => s!"\"{PyName name}\""
  | .option .string => "str"
  | .option t => s!"Optional[{genType t}]"
  | .list .string => "list[str]"
  | .list t => s!"list[{genType t}]"
  | .pair .. => panic! "TODO"

private def under (s : String) : String :=
  if s == "" || s.endsWith "_" then s
  else s ++ "_"

private def genPyType (ty : LeanType) (pre : String := "") : MetaM Unit :=
  match ty with
  | .simple _ => pure ()
  | .prod name fields => do
      IO.println ""
      IO.println s!"class {under pre}{name}(NamedTuple):"
      if fields.length == 0 then
        IO.println "  pass"
      for f in fields do
        IO.println s!"  {f.name} : {genType f.type}"
  | .sum name variants => do
      if ty.isEnum then do
        IO.println ""
        IO.println s!"class {name}(Enum):"
        for v in variants do
          IO.println s!"  {(toString v.name).capitalize} = auto()"
        IO.println ""
        for v in variants do
          IO.println s!"def {name}_{v.name}(): return {name}.{(toString v.name).capitalize}"
      else do
        let mut tys := []
        for v in variants do
          genPyType v (PyName name)
          tys := (under (PyName name) ++ PyName v.name) :: tys
        let rhs := String.intercalate " | " tys
        IO.println ""
        IO.println s!"{name} = {rhs}"
        return ()

private def header :=
"# This file is automatically generated from KLR
# Manual edits will be overwritten

from typing import NamedTuple, Optional
from enum import Enum, auto"

def generatePythonAST : MetaM Unit := do
  IO.println header
  let tys <- C.pythonAST
  let pty <- collectLeanType `KLR.Core.Pos
  for t in pty :: tys do
    genPyType t
  return ()

def generateNkiAST : MetaM Unit := do
  IO.println header
  let tys <- C.nkiAST
  let pty <- collectLeanType `KLR.Core.Pos
  for t in pty :: tys do
    genPyType t
  return ()
