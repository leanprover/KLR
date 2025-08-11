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
import KLR.Compile
import TensorLib.Npy
import TensorLib.Tensor

open Cli
open KLR
open System(FilePath)

inductive Form where
| json
| pretty

def asString [Lean.ToJson a] [Repr a] (p : Parsed) (x : a) (defaultForm : Form := .pretty) : String :=
  let fm := if p.hasFlag "pretty" then .pretty
            else if p.hasFlag "json" then .json
            else defaultForm
  match fm with
  | .json => toString $ Lean.toJson x
  | .pretty => reprStr x

def writeContent (ext : String) (p : Parsed) (content : String) : IO Unit := do
  match p.flag? "outfile" with
  | some arg =>
    let f := (FilePath.mk (arg.as! String)).withExtension ext
    IO.FS.writeFile f content
  | none =>
    IO.println content


/-
We have a mix of Python and Lean executables, so need to worry about
PYTHONPATH. In the Bash/Python gather exe below, we expect input of the
form

    # bin/gather my_kernel_module my_kernel_function output_file

It is natural to expect being able to pass a file name here, but that
doesn't work; we expect the module's file to be on PYTHONPATH.

From Lean, we will take a filename and a kernel name, and muck with
the PYTHONPATH accordingly.
-/

def gatherTmp [KLR.File.FromContents a] (p : Parsed) : IO a := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  IO.FS.withTempFile fun _ tmpName => do
    gatherRun file kernel tmpName.toString dir debug
    KLR.File.readKLRFile tmpName .cbor

def gather (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  let outFile := (p.flag? "outfile").map fun x => x.as! String
  let outFile := outFile.getD (kernel ++ ".klr")
  gatherRun file kernel outFile dir debug
  return 0

def info (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let dump := p.flag? "dump"
  let arr <- IO.FS.readBinFile file
  let contents <- KLR.File.parseBytes arr .cbor

  -- handle content dump
  if let some format := dump then
    match format.as? String with
    | some "json" => IO.println <| Lean.toJson contents
    | some "nki" => throw (.userError "NKI prettry printing not yet implemented")
    | some "repr" => IO.println <| reprStr contents
    | some "sexp" => IO.println <| KLR.Util.toSexp contents
    | some format => throw (.userError s!"unsupported format {format}")
    | none => throw (.userError "expecting format argument")
    return 0

  -- handle summmary
  match contents with
  | .python kernel =>
    IO.println s!"AST summary for Python Core kernel {kernel.entry}"
    let fs := String.intercalate "," $ kernel.funcs.map fun f => f.name
    IO.println s!"Source Functions: {fs}"
    let gs := String.intercalate "," $ kernel.globals.map fun kw => kw.id
    IO.println s!"Globals: {gs}"
  | .nki kernel =>
    IO.println s!"AST summary for NKI kernel {kernel.entry}"
    let fs := String.intercalate "," $ kernel.funs.map fun f => f.name
    IO.println s!"Source Functions: {fs}"
    let gs := String.intercalate "," $ kernel.globals.map fun kw => kw.name
    IO.println s!"Globals: {gs}"
  | .hlo name =>
    IO.println s!"HLO Call Site {name}"
  | .klir kernel =>
    IO.println s!"AST summary for KLIR kernel {kernel.name}"
  return 0

def compile (p : Parsed) : IO UInt32 := do
  let kernel : KLR.Python.Kernel <- gatherTmp p
  let _kernel <- compilePython kernel
  return 0

def trace (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let kernel <- KLR.File.readKLRFile file
  let kernel <- compilePython kernel
  match p.flag? "outfile" with
  | some arg =>
    let f := FilePath.mk (arg.as! String)
    IO.println (reprStr kernel)
    File.writeKLRFile f .cbor kernel
  | none =>
    IO.println (reprStr kernel)
  return 0

private def evalKlrTensors
  (p : Parsed)
  (npyInputFiles : List String)
  : IO (List (String × TensorLib.Tensor)) := do
  let kernel : KLR.NKI.Kernel <- gatherTmp p
  --let (k, warnings1) := kernel.inferArguments
  let (warnings, klr) <- KLR.Trace.runNKIKernel kernel
  dbg_trace s!"klr-inputs: {repr klr.inputs}"
  --if !warnings1.isEmpty then IO.eprintln warnings1
  if !warnings.isEmpty then IO.eprintln warnings
  let inputs := npyInputFiles.map FilePath.mk
  let npys <- inputs.mapM TensorLib.Npy.parseFile
  let inputs <- npys.mapM fun npy => TensorLib.Tensor.ofNpy npy
  dbg_trace s!"npy-inputs: {repr inputs}"
  --let _ <- KLR.Eval.eval klr inputs
  IO.println "TODO: UNIMPLEMENTED"
  return []

def evalKLR (p : Parsed) : IO UInt32 := do
  let outputDir := (p.flag? "output-dir").map fun x => x.as! String
  let inputs := (p.variableArgsAs! String).toList
  let outputs := (p.flag? "output-names").map fun f => (f.as! (Array String)).toList
  let resultMap <- evalKlrTensors p inputs
  let n := resultMap.length
  let outputs :=
    let outputs := outputs.getD []
    if n <= outputs.length then outputs else
    let k := n - outputs.length
    outputs ++ ((List.range k).map fun i => s!"output-{outputs.length + i}")
   -- ignore the inferred name from the kernel
  (resultMap.zip outputs).forM fun ((_, t), name) => do
    let arr := TensorLib.Tensor.toNpy t
    let filename := match outputDir with
    | .none => s!"{name}.npy"
    | .some d => s!"{d}/{name}.npy"
    IO.println s!"Writing file {filename}"
    TensorLib.Npy.Ndarray.save! arr filename
  return 0

-- -- Command configuration

def gatherCmd := `[Cli|
  "gather" VIA gather;
  "Gather Python sources into an AST file"

  FLAGS:
    o, outfile : String; "Name of output file"
    d, "klr-module-dir" : String; "Directory of Python klr module. Added to PYTHONPATH."
    debug : Unit; "Print debugging info"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionName : String; "Name of the kernel function"
]

def compileCmd := `[Cli|
  "compile" VIA compile;
  "Compile a NKI kernel"

  FLAGS:
    o, outfile : String; "Name of output file"
    d, "klr-module-dir" : String; "Directory of Python klr module. Added to PYTHONPATH."
    debug : Unit; "Print debugging info"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionName : String; "Name of the kernel function"
]

def infoCmd := `[Cli|
  "info" VIA info;
  "Display information about a KLR file"

  FLAGS:
    d, dump : String; "Output entire contents, format: json, nki, repr, sexp"
  ARGS:
    file : String; "KLR format input file"
]

def traceCmd := `[Cli|
  "trace" VIA trace;
  "Trace Python to KLR"

  FLAGS:
    o, outfile : String; "Name of output file"
    p, pretty; "Output human-readable format (do not generate output file)"
  ARGS:
    file : String; "File of Python AST printed as JSON"
]

def evalKLRCmd := `[Cli|
  "eval-klr" VIA evalKLR;
  "Evaluate a kernel using a pure-Lean KLR interpreter. Outputs one npy file for each output."

  FLAGS:
    "klr-module-dir" : String; "Directory of Python klr module. Added to PYTHONPATH."
    debug : Unit; "Print debugging info"
    "output-dir" : String; "Where to write npy files. Defaults to cwd."
    "output-names" : Array String; "Names of output npy files to write to disk. E.g. --outputs a,b will " ++
                                   "write a.npy and b.npy with the contents of arrays `a` and `b`."
  ARGS:
    moduleFileName : String;      "File of the Python module with the kernel function"
    kernelFunctionName : String;  "Name of the kernel function"
    ...inputFiles : String;       ".npy files corresponding to the inputs to the kernel, in positional order"
]

def klrCmd : Cmd := `[Cli|
  klr NOOP; ["0.0.12"]
  "KLR is an IR for NKI and other tensor-like languages in Lean."

  SUBCOMMANDS:
    compileCmd;
    evalKLRCmd;
    gatherCmd;
    infoCmd;
    traceCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then do
    IO.println klrCmd.help
    return 0

  try klrCmd.validate args
  catch e =>
    match e with
    | .userError s => IO.eprintln s
    | e => IO.eprintln s!"{e}"
    pure 1
