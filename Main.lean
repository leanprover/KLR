import KLR
import KLR.BIR.Compile
import Cli
import KLR.Eval
import KLR.NEFF
import KLR.Util
import KLR.Util.Gzip
import TensorLib.Npy
import TensorLib.Tensor

open Cli
open KLR
open System(FilePath)

local instance : MonadLift Err IO where
  monadLift
    | .ok x => return x
    | .error s => throw $ .userError s

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

def eprintln [ToString a] (debug : Bool) (x : a) : IO Unit := do
  if debug then IO.eprintln x

/-
We have a mix of Python and Lean executables, so need to worry about
PYTHONPATH. In the Bash/Python gather exe below, we expect input of the
form

    # bin/gather my_kernel_module.my_kernel_function

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
  | [] => impossible
  | [f] => ([], f)
  | f :: dirs => (dirs.reverse, f)
  let (file, ext) := match (file.splitOn ".").reverse with
  | [] => impossible
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

def gatherStr (moduleFileName kernelFunctionName : String) (klrPythonModuleDir : Option String) (debug : Bool) : IO String := do
  let dbg := eprintln debug
  let pypath <- IO.getEnv "PYTHONPATH"
  let pypath := pypath.getD ""
  let parts := FileNameParts.make moduleFileName
  dbg $ "parts: " ++ repr parts
  let gather1 := (<- IO.appPath).parent.get!.join "gather"
  let gather2 := (<- IO.currentDir).join "bin/gather"
  -- The directory of the kernel file must be on PYTHONPATH
  let pypath := match parts.dirs with
  | [] => pypath
  | _ => pypath ++ ":" ++ parts.dir
  -- The klr directory must also be there. A better implementation would check to see if it's on
  -- the path already without adding `interop`
  let klrDir := klrPythonModuleDir.getD "interop" -- interop is the project default
  let pypath := pypath ++ ":" ++ klrDir
  let gatherArg := parts.fileNameNoExt ++ "." ++ kernelFunctionName
  for exe in [gather1, gather2] do
    dbg $ "exe: " ++ exe.toString
    dbg $ "pypath: " ++ pypath
    if <- exe.pathExists then
      let output <- IO.Process.output {
        cmd := exe.toString
        args := #[ gatherArg ]
        env := #[ ("PYTHONPATH", some pypath) ]
      }
      if output.exitCode != 0 then
        IO.println output.stderr
        IO.throwServerError "error gathering kernel"
      dbg $ "stdout: " ++ output.stdout
      dbg $ "stderr: " ++ output.stderr
      return output.stdout
  IO.throwServerError "could not find gather program"

private def evalKlrTensors
  (moduleFileName kernelFunctionName : String)
  (klrPythonModuleDir : Option String)
  (debug : Bool)
  (npyInputFiles : List String)
   : IO (List (String × TensorLib.Tensor)) := do
  let s <- gatherStr moduleFileName kernelFunctionName klrPythonModuleDir debug
  let kernel <- KLR.Python.Parsing.parse s
  let (k, warnings1) := kernel.inferArguments
  let (warnings, klr) <- KLR.Trace.runNKIKernel k
  dbg_trace s!"klr-inputs: {repr klr.inputs}"
  if !warnings1.isEmpty then IO.eprintln warnings1
  if !warnings.isEmpty then IO.eprintln warnings
  let inputs := npyInputFiles.map FilePath.mk
  let npys <- inputs.mapM TensorLib.Npy.parseFile
  let inputs <- npys.mapM fun npy => TensorLib.Tensor.ofNpy npy
  dbg_trace s!"npy-inputs: {repr inputs}"
  KLR.Eval.eval klr inputs

def gather (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  let output <- gatherStr file kernel dir debug
  writeContent "ast" p output
  return 0

private def parse (p : Parsed) : IO KLR.Python.Kernel := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  KLR.Python.Parsing.parse s

def parseAST (p : Parsed) : IO UInt32 := do
  let kernel <- parse p
  if p.hasFlag "verbose" then
    IO.println s!"{repr kernel}"
    return 0
  IO.println s!"AST summary for kernel {kernel.entry}"
  let fs := String.intercalate "," $ kernel.funcs.map fun f => f.name
  IO.println s!"Source Functions: {fs}"
  let gs := String.intercalate "," $ kernel.globals.map fun kw => kw.id
  IO.println s!"Globals: {gs}"
  IO.println s!"Undefined names {kernel.undefinedSymbols.mergeSort}"
  return 0

def trace (p : Parsed) : IO UInt32 := do
  let kernel <- parse p
  let (k, warnings1) := kernel.inferArguments
  let (warnings, klr) <- KLR.Trace.runNKIKernel k
  if !warnings.isEmpty then IO.eprintln warnings
  if !warnings1.isEmpty then IO.eprintln warnings1
  writeContent "klr" p (asString p klr)
  return 0

def parseKLR (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  let json <- Lean.Json.parse s
  if p.hasFlag "json" then
    IO.println json
    return 0
  let klr : Core.Kernel <- Lean.fromJson? (<- Lean.Json.parse s)
  IO.println $ asString p klr
  return 0

/-
Generate a filename for this invocation of the kernel. The hash value is
generated from the json string from gather. This may be different for
equivalent invocations of the kernel, but this is OK: it is wasteful but not
incorrect.
-/
private def klrFilename (p : Parsed) (hash: UInt64) : FilePath :=
  let hash := hash.toBitVec.toHex
  let file := (FilePath.mk hash).withExtension "klr"
  let dir :=
    match p.flag? "dir" with
    | none => FilePath.mk "."
    | some d => FilePath.mk (d.as! String)
  (dir / file).normalize

-- This is used by the python code
def traceAPI (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  let outfile := klrFilename p s.hash
  if <- outfile.pathExists then
    IO.eprintln "file exists: tracing skipped"
    IO.println outfile
    return 0
  let kernel <- KLR.Python.Parsing.parse s
  let (warnings, klr) <- KLR.Trace.runNKIKernel kernel
  IO.FS.writeFile outfile (toString $ Lean.toJson klr)
  IO.eprintln warnings
  IO.println outfile
  return 0

def compile (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  let klr <- Lean.fromJson? (<- Lean.Json.parse s)
  let bir <- KLR.BIR.compile klr
  writeContent "bir" p (toString $ Lean.toJson bir)
  return 0

def parseBIR (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let str <- IO.FS.readFile file
  let json <- Lean.Json.parse str
  let bir : KLR.BIR.BIR <- Lean.fromJson? json
  IO.println $ asString p bir
  return 0

def neffInfo (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let neff <- NEFF.File.read file
  IO.println (repr neff)
  return 0

def nkiToKLR (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  let s <- gatherStr file kernel dir debug
  let kernel <- KLR.Python.Parsing.parse s
  let (k, warnings1) := kernel.inferArguments
  let (warnings, klr) <- KLR.Trace.runNKIKernel k
  writeContent "klr" p (asString p klr)
  if !warnings.isEmpty then IO.eprintln warnings
  if !warnings1.isEmpty then IO.eprintln warnings1
  return 0

def evalKLR (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let kernelDir := (p.flag? "klr-module-dir").map fun x => x.as! String
  let outputDir := (p.flag? "output-dir").map fun x => x.as! String
  let inputs := (p.variableArgsAs! String).toList
  let outputs := (p.flag? "output-names").map fun f => (f.as! (Array String)).toList
  let resultMap <- evalKlrTensors file kernel kernelDir debug inputs
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

def parseASTCmd := `[Cli|
  "parse-ast" VIA parseAST;
  "Parse Python AST file"

  FLAGS:
    v, verbose; "Output complete AST information"
  ARGS:
    file : String;      "File of gathered Python AST"
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

def parseKLRCmd := `[Cli|
  "parse-klr" VIA parseKLR;
  "Display information about a KLR file"

  FLAGS:
    j, json; "Output Json format"
    p, pretty; "Output human-readable format (default)"
  ARGS:
    file : String; "File of Python AST printed as JSON"
]

def traceAPICmd := `[Cli|
  "trace-api" VIA traceAPI;
  "Trace Python to KLR (API version)"

  FLAGS:
    d, dir : String; "Directory to write KLR file to"
  ARGS:
    file : String; "File of Python AST printed as JSON"
]

def compileCmd := `[Cli|
  "compile" VIA compile;
  "Compile Python to BIR"

  FLAGS:
    o, outfile : String; "Name of output file"
  ARGS:
    file : String; "File of Python AST printed as JSON"
]

def parseBIRCmd := `[Cli|
  "parse-bir" VIA parseBIR;
  "Parse a BIR Json file"

  FLAGS:
    j, json; "Output JSON format"
    p, pretty; "Output human-readable format (default)"
  ARGS:
    file : String; "File of BIR JSON"
]

def neffInfoCmd := `[Cli|
  "neff-info" VIA neffInfo;
  "Parse a NEFF file"

  ARGS:
    file : String; "NEFF file"
]

def nkiToKLRCmd := `[Cli|
  "nki-to-klr" VIA nkiToKLR;
  "Compile NKI kernel to KLR"

  FLAGS:
    d, "klr-module-dir" : String; "Directory of Python klr module. Added to PYTHONPATH."
    debug : Unit; "Print debugging info"
    o, outfile : String; "Name of output file"
    j, json; "Output JSON format"
    p, pretty; "Output human-readable format (default)"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionName : String; "Name of the kernel function"
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
  klr NOOP; ["0.0.9"]
  "KLR is an IR for NKI and other tensor-like languages in Lean."

  SUBCOMMANDS:
    compileCmd;
    evalKLRCmd;
    gatherCmd;
    neffInfoCmd;
    nkiToKLRCmd;
    parseASTCmd;
    parseKLRCmd;
    parseBIRCmd;
    traceCmd;
    traceAPICmd
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
