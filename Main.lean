import KLR
import KLR.BIR.Compile
import Cli
import KLR.Util

open KLR
open Cli

local instance : MonadLift Err IO where
  monadLift
    | .ok x => return x
    | .error s => throw $ .userError s

def showAs [Lean.ToJson a] [Repr a] (p : Parsed) (x : a) : IO Unit :=
  if p.hasFlag "repr" then
    IO.println (toString $ repr x)
  else if p.hasFlag "json" then
    IO.println (toString $ Lean.toJson x)
  else
    -- For now, default is JSON, but we may change this
    IO.println (toString $ Lean.toJson x)

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
      dbg $ "stdout: " ++ output.stdout
      dbg $ "stderr: " ++ output.stderr
      return output.stdout
  IO.throwServerError "could not find gather program"

def gather (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  try
    let output <- gatherStr file kernel dir debug
    IO.println output
    return 0
  catch
  | IO.Error.userError s =>
    IO.println s
    return 1
  | err =>
    IO.println err
    return 1

private def parse (p : Parsed) : IO KLR.Python.Kernel := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  KLR.Python.Parsing.parse s

def parseJson (p : Parsed) : IO UInt32 := do
  let kernel <- parse p
  let klr <- KLR.Trace.runNKIKernel kernel.inferArguments
  let json := Lean.toJson klr
  IO.println json
  return 0

def trace (p : Parsed) : IO UInt32 := do
  let kernel <- parse p
  let klr <- KLR.Trace.runNKIKernel kernel.inferArguments
  showAs p klr
  return 0

def parseBIR (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let str <- IO.FS.readFile file
  let json <- Lean.Json.parse str
  let bir : KLR.BIR.BIR <- Lean.fromJson? json
  showAs p bir
  return 0

def compileStr (s : String) : Err KLR.BIR.BIR := do
  let kernel <- KLR.Python.Parsing.parse s
  let klr <- KLR.Trace.runNKIKernel kernel.inferArguments
  KLR.BIR.compile klr

def compile (p : Parsed) : IO UInt32 := do
  let file := p.positionalArg! "file" |>.as! String
  let s <- IO.FS.readFile file
  let bir <- compileStr s
  showAs p bir
  return 0

def nkiToBIR (p : Parsed) : IO UInt32 := do
  let debug := p.hasFlag "debug"
  let file := p.positionalArg! "moduleFileName" |>.as! String
  let kernel := p.positionalArg! "kernelFunctionName" |>.as! String
  let dir := (p.flag? "klr-module-dir").map fun x => x.as! String
  let s <- gatherStr file kernel dir debug
  let bir <- compileStr s
  showAs p bir
  return 0

-- -- Command configuration

def gatherCmd := `[Cli|
  "gather" VIA gather;
  "Gather Python sources into a JSON file"

  FLAGS:
    d, "klr-module-dir" : String; "Directory of Python klr module. Added to PYTHONPATH."
    debug : Unit; "Print debugging info"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionName : String; "Name of the kernel function"
]

def parseJsonCmd := `[Cli|
  "parse-json" VIA parseJson;
  "Parse KLR kernels as JSON"

  ARGS:
    file : String;      "File of Python AST printed as JSON"
]

def traceCmd := `[Cli|
  "trace" VIA trace;
  "Trace Python to KLR"

  FLAGS:
    r, repr; "Output Repr format"
    j, json; "Output Json format"
  ARGS:
    file : String; "File of Python AST printed as JSON"
]

def parseBIRCmd := `[Cli|
  "parse-bir" VIA parseBIR;
  "Parse a BIR Json file"

  FLAGS:
    r, repr; "Output Repr format"
  ARGS:
    file : String; "File of BIR JSON"
]

def compileCmd := `[Cli|
  "compile" VIA compile;
  "Compile Python to BIR"

  FLAGS:
    r, repr; "Output Repr format"
  ARGS:
    file : String; "File of Python AST printed as JSON"
]

def nkiToBIRCmd := `[Cli|
  "nki-to-bir" VIA nkiToBIR;
  "Compile NKI kernel in Python to BIR"

  FLAGS:
    d, "klr-module-dir" : String; "Directory of Python klr module. Added to PYTHONPATH."
    r, repr; "Output Repr format, instead of JSON"
    debug : Unit; "Print debugging info"

  ARGS:
    moduleFileName : String; "File of the Python module with the kernel function"
    kernelFunctionName : String; "Name of the kernel function"
]

def klrCmd : Cmd := `[Cli|
  klr NOOP; ["0.0.7"]
  "KLR is an IR for NKI and other tensor-like languages in Lean."

  SUBCOMMANDS:
    compileCmd;
    gatherCmd;
    nkiToBIRCmd;
    parseBIRCmd;
    parseJsonCmd;
    traceCmd
]

def main (args : List String) : IO UInt32 :=
  if args.isEmpty then do
    IO.println klrCmd.help
    return 0
  else do
    klrCmd.validate args
