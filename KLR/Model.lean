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
import KLR.Python
import KLR.NKI
open Cli

def modelKLR (p : Parsed) : IO UInt32 := do
  /- Load the Python file and perform simplifications -/
  let kernel : KLR.Python.Kernel <- gatherTmp p
  -- IO.println s!"[Kernel] \n{Lean.toJson kernel}"
  let (kernel, warnings) := kernel.inferArguments
  warnings.forM IO.eprintln
  let kernel : KLR.NKI.Kernel <- KLR.NKI.simplify kernel
  let (kernel, w) <- KLR.NKI.simplifyOperators kernel
  w.forM IO.println
  let kernel <- KLR.NKI.annotate kernel
  let kernel <- KLR.NKI.simplifyPatterns kernel
  -- IO.println s!"{Lean.toJson kernel}"
  match (NKI.model kernel : Err NMLModel) with
  | .error s => throw <| (IO.userError s)
  | .ok m =>
  writeContent "lean" p (NKI.pprint_standalone_model m)
  return 0

def equivKLR (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernelL := p.positionalArg! "kernelFunctionNameL" |>.as! String
  let kernelR := p.positionalArg! "kernelFunctionNameR" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  let kernelL : KLR.Python.Kernel ← IO.FS.withTempFile fun _ tmpName => do
    gatherRun file kernelL tmpName.toString dir debug
    KLR.File.readKLRFile tmpName .cbor
  let kernelR : KLR.Python.Kernel ← IO.FS.withTempFile fun _ tmpName => do
    gatherRun file kernelR tmpName.toString dir debug
    KLR.File.readKLRFile tmpName .cbor
  let (kernelL, warnings) := kernelL.inferArguments
  warnings.forM IO.eprintln
  let (kernelR, warnings) := kernelR.inferArguments
  let kernelL : KLR.NKI.Kernel <- KLR.NKI.simplify kernelL
  let kernelR : KLR.NKI.Kernel <- KLR.NKI.simplify kernelR
  let (kernelL, w) <- KLR.NKI.simplifyOperators kernelL
  w.forM IO.println
  let (kernelR, w) <- KLR.NKI.simplifyOperators kernelR
  w.forM IO.println
  let kernelL <- KLR.NKI.annotate kernelL
  let kernelR <- KLR.NKI.annotate kernelR
  let kernelL <- KLR.NKI.simplifyPatterns kernelL
  let kernelR <- KLR.NKI.simplifyPatterns kernelR
  match (NKI.model kernelL : Err NMLModel) with
  | .error s => throw <| (IO.userError s)
  | .ok mL =>
  match (NKI.model kernelR : Err NMLModel) with
  | .error s => throw <| (IO.userError s)
  | .ok mR =>
  writeContent "lean" p (NKI.pprint_relational_goal mL mR)
  return 0

def modelKLRCmd:= `[Cli|
  "model" VIA modelKLR;
  "Emit a Lean model of a KLR kernel which describes its semantics exactly."

  FLAGS:
    o, outfile : String; "Name of output file"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionName : String; "Name of the kernel function"
]

def equivKLRCmd:= `[Cli|
  "equiv" VIA equivKLR;
  "Emit a Lean file containing an open theorem that two KLR kernels are equivalent."

  FLAGS:
    o, outfile : String; "Name of output file"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionNameL : String; "Name of the left kernel function"
    kernelFunctionNameR : String; "Name of the right kernel function"
]
