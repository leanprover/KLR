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
import TensorLib.Npy
import TensorLib.Tensor

open Cli
open KLR
open System(FilePath)

inductive Form where
| json
| pretty

def eprintln [ToString a] (debug : Bool) (x : a) : IO Unit := do
  if debug then IO.eprintln x

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

structure FileNameParts where
  private mk::
  dirs : List String
  fileNameNoExt : String
  ext : Option String
  deriving BEq, Inhabited, Repr

namespace FileNameParts

def fileName (parts : FileNameParts) : String := match parts.ext with
| none => parts.fileNameNoExt
| some ext => parts.fileNameNoExt ++ "." ++ ext

def make (file : String) : FileNameParts :=
  let (dirs, file) := match (file.splitOn "/").reverse with
  | [] => impossible file
  | [f] => ([], f)
  | f :: dirs => (dirs.reverse, f)
  let (file, ext) := match (file.splitOn ".").reverse with
  | [] => impossible file
  | [f] => (f, none)
  | ext :: fs => (String.intercalate "." fs.reverse, some ext)
  FileNameParts.mk dirs file ext

def dir (parts : FileNameParts) : String := String.intercalate "/" parts.dirs

def pathToFile (parts : FileNameParts) : String :=
  String.intercalate "." (parts.dirs ++ [parts.fileNameNoExt] ++ parts.ext.toList)

#guard FileNameParts.make "foo" == FileNameParts.mk [] "foo" none
#guard FileNameParts.make "foo/bar" == FileNameParts.mk ["foo"] "bar" none
#guard FileNameParts.make "a/b/c.bar" == FileNameParts.mk ["a", "b"] "c" (some "bar")
#guard (FileNameParts.make "a.b.c.bar").pathToFile == "a.b.c.bar"
#guard (FileNameParts.make "a/b/c.bar").dir == "a/b"

end FileNameParts

/-
If we are in a python environment with a pip installed version of klr-lang,
then we should have a program called klr-gather on the path; this script is
installed in the python bin directory as part of the wheel installation. If we
don't find the program on the PATH, then we try to use ./bin/gather, which will
work for local developers using "lake exe klr".
-/
def gatherRun (moduleFileName kernelFunctionName outputFileName: String)
              (klrPythonModuleDir : Option String) (debug : Bool) : IO Unit := do
  let dbg := eprintln debug
  let pypath <- IO.getEnv "PYTHONPATH"
  let pypath := pypath.getD ""
  let parts := FileNameParts.make moduleFileName
  dbg $ "parts: " ++ repr parts
  let gather := FilePath.mk "klr-gather"
  let localBin := (<- IO.currentDir).join "bin"
  -- The directory of the kernel file must be on PYTHONPATH
  let pypath := match parts.dirs with
  | [] => pypath
  | _ => pypath ++ ":" ++ parts.dir
  -- The klr directory must also be there. A better implementation would check to see if it's on
  -- the path already without adding `interop`
  let klrDir := klrPythonModuleDir.getD "interop" -- interop is the project default
  let pypath := pypath ++ ":" ++ klrDir
  dbg $ "pypath: " ++ pypath

  let gatherArg := #[ parts.fileNameNoExt, kernelFunctionName, outputFileName ]
  let path <- IO.getEnv "PATH"
  let paths := path.get!.splitOn ":"
  let paths := paths.map FilePath.mk ++ [localBin]
  for p in paths do
    let exe := p.join gather
    dbg $ "exe: " ++ exe.toString
    if <- exe.pathExists then
      let output <- IO.Process.output {
        cmd := exe.toString
        args := gatherArg
        env := #[ ("PYTHONPATH", some pypath) ]
      }
      if output.exitCode != 0 then
        IO.println output.stderr
        IO.throwServerError "error gathering kernel"
      dbg $ "stderr: " ++ output.stderr
      return ()
  IO.throwServerError "could not execute gather program"

def gatherTmp (p : Parsed) : IO Python.Kernel := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  IO.FS.withTempFile fun _ tmpName => do
    gatherRun file kernel tmpName.toString dir debug
    let contents <- IO.FS.readFile tmpName
    Lean.fromJson? (<- Lean.Json.parse contents)

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
    let gs := String.intercalate "," $ kernel.globals.map fun kw => kw.id.get!
    IO.println s!"Globals: {gs}"
  | .nki kernel =>
    IO.println s!"AST summary for NKI kernel {kernel.entry}"
    let fs := String.intercalate "," $ kernel.funs.map fun f => f.name.toString
    IO.println s!"Source Functions: {fs}"
    let gs := String.intercalate "," $ kernel.globals.map fun kw => kw.name
    IO.println s!"Globals: {gs}"
  | .hlo name =>
    IO.println s!"HLO Call Site {name}"
  | .kernel kernel =>
    IO.println s!"AST summary for NKI-IR kernel {kernel.name}"
  | .lnc kernel =>
    IO.println s!"AST summary for NKI-IR LNC kernel {kernel.name}"
  return 0

def compile (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let kernel : KLR.Python.Kernel <- gatherTmp p
  let res <- KLR.Compile.compilePython kernel none none
  let kernel <- res.result
  IO.println "OK."
  if debug then
    IO.println s!"Kernel:\n {repr kernel}"
  match p.flag? "outfile" with
  | some arg => File.writeKLRFile (arg.as! String) .cbor kernel
  | none => pure ()
  return 0

private def outfolder (outfile : Option Parsed.Flag) : IO (Option String) := do
  match outfile with
  | some p =>
    let path := FilePath.mk (p.as! String)
    if path.parent == none then return "."
    if path.parent == FilePath.mk "." then return "."
    return path.parent.map toString
  | none => return none

def trace (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let contents <- IO.FS.readFile file
  let kernel <- Lean.fromJson? (<- Lean.Json.parse contents)
  --let kernel <- KLR.File.readKLRFile file
  let outDir := <- outfolder (p.flag? "outfile")
  let res <- KLR.Compile.compilePython kernel outDir none
  for e in res.warnings do IO.println e
  for e in res.messages do IO.println e
  for e in res.errors do IO.println e
  let kernel <- res.result
  match p.flag? "outfile" with
  | some arg =>
    let f := FilePath.mk (arg.as! String)
    File.writeKLRFile f .cbor kernel
  | none =>
    pure () --IO.println (reprStr kernel)
  return 0

def listBuiltins (_ : Parsed) : IO UInt32 := do
  let mut cs := #[]
  let mut max := 0
  for (n,t) in Trace.globalEnv do
    cs := cs.push (t.kindStr, n.toString)
    let s := t.kindStr
    if s.length >= max then
      max := s.length + 1
  let lines := cs.map fun (k, n) => s!"{k.pushn ' ' (max - k.length)} {n}"
  lines.toList.mergeSort.forM IO.println
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

def listCmd := `[Cli|
  "list" VIA listBuiltins;
  "List builtin functions and constants"
]

def klrCmd : Cmd := `[Cli|
  klr NOOP; ["0.0.12"]
  "KLR is an IR for NKI and other tensor-like languages in Lean."

  SUBCOMMANDS:
    compileCmd;
    gatherCmd;
    infoCmd;
    traceCmd;
    listCmd
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
