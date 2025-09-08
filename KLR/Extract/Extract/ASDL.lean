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
import Lean

/-
Output functions for ASDL
-/

namespace Extract.ASDL
open Lean Meta

local instance : ToString Name where
  toString
  | .str _ s => s
  | n => n.toString

private def typeName (ty : SimpleType) : String :=
  match ty with
  | .option t => typeName t ++ "?"
  | .list t => typeName t ++ "*"
  | _ => s!"{ty.name}"


private def genType (ty : LeanType) (topLevel : Bool := false) : MetaM Unit :=
  match ty with
  | .simple _ => pure ()
  | .prod name fields => do
      if topLevel then
        IO.print s!"\n{name} = ("
      else
        IO.print s!"{name}("
      for f in fields do
        IO.print s!"{typeName f.type} {f.name}, "
      IO.println ")"
  | .sum name variants => do
      if ty.isEnum then do
        IO.println s!"{name} ="
        for v in variants do
          IO.println s!"  | {v.name}"
      else do
        IO.println s!"{name} ="
        for v in variants do
          IO.print s!" | "
          genType v
        IO.println ""
        return ()

def generateNkiAST : MetaM Unit := do
  let tys <- klrAST
  for t in tys do
    genType t (topLevel := true)
  return ()

-- NOTE: Uncomment for debugging
-- run_meta generateNkiAST
