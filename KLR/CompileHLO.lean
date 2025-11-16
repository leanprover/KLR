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

import Cli
import KLR
import SHerLOC
import KLR.TGR.Basic
import SHerLOC.Analysis.Graph
import KLR.K.K3.CompileK3
import KLR.K.K2.CompileK2
import KLR.K.K2.AST
import KLR.K.K3.DotK3
import KLR.K.K1.CompileK1
import KLR.K.K1.AST
import KLR.K.K1.InterpK1

private def unwrap {T Q : Type} [Inhabited T] [Inhabited Q]
  (x : Except String T × Q) : T × Q :=
  match x with
  | (.ok a, s)  => (a, s)
  | (.error e, _) => panic! s!"Error: {e}"

def compileHlo (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  match StableHLO.Parsing.parse s with
  | .ok (hlo, _) =>
    -- compile HLO to TGR
    let (_, s) := KLR.TGR.Compile.compile hlo |> unwrap
    let func := s.program.functions.head!
    if p.hasFlag "intermediates" then
      writeContent "tgr.txt" p (toString s.program)
      writeContent "tgr.dot" p s!"{KLR.TGR.Graph.graph func}"
      writeContent "py" p (KLR.TGR.Py.compile s.program)
    -- compile TGR to K3
    IO.println s!"Compiling TGR to K3"
    let (func, _) := KLR.K.K3.compile func |> unwrap
    if p.hasFlag "intermediates" then
      writeContent "k3.txt" p s!"{func}"
      writeContent "k3.dot" p (KLR.K.K3.graph func |> toString)
    -- compile K3 to K2
    IO.println s!"Compiling K3 to K2"
    let (func, _) := KLR.K.K2.compile func |> unwrap
    if p.hasFlag "intermediates" then
      writeContent "k2.txt" p s!"{KLR.K.K2.formatProgramK2 func}"
    -- compile K2 to K1
    IO.println s!"Compiling K2 to K1"
    let (func, _) := KLR.K.K1.compile func |> unwrap
    writeContent "k1.txt" p s!"{KLR.K.K1.formatProgramK1 func}"
    if p.hasFlag "evaluate" then
      IO.println s!"Evaluating K1"
      match KLR.K.K1.Interp.interp func with
      | (.ok (), ctx) =>
        writeContent "k1.result" p s!"{ctx}"
      | (.error e, ctx) =>
        IO.eprintln s!"Error interpreting K1: {e}"
        writeContent "k1.err" p s!"{ctx}"
    return 0
  | .error e =>
    IO.eprintln s!"Error parsing HLO: {e}"
    return 1

def compileHloCmd := `[Cli|
  "compile-hlo" VIA compileHlo;
  "Compile HLO graph to KLR graph"

  FLAGS:
    o, outfile : String; "Name of output file"
    i, intermediates : Unit; "Write intermediate files"
    e, evaluate : Unit; "Evaluate the K1 program on random inputs as a smoke test"
  ARGS:
    file : String;      "File of HLO graph in .mlir format"
]
