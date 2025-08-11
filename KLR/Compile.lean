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

import KLR
open KLR
open System(FilePath)

def eprintln [ToString a] (debug : Bool) (x : a) : IO Unit := do
  if debug then IO.eprintln x

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

-- TODO: preserve warnings and errors
def compilePython (kernel : Python.Kernel) : IO Core.Kernel := do
  let (kernel, warnings) := kernel.inferArguments
  warnings.forM IO.eprintln
  let kernel : KLR.NKI.Kernel <- KLR.NKI.simplify kernel
  let (kernel, w) <- KLR.NKI.simplifyOperators kernel
  w.forM IO.println
  let kernel <- KLR.NKI.annotate kernel
  let kernel <- KLR.NKI.simplifyPatterns kernel
  -- Leave in for debugging
  -- TODO use debug flags?
  --IO.println (Std.Format.pretty (Std.format kernel))
  --IO.println (reprStr kernel)
  let (warnings, kernel) <- KLR.Trace.runNKIKernel kernel
  if !warnings.isEmpty then
    IO.eprintln warnings
  let kernel <- Core.lowerAccessPatterns kernel
  return kernel

@[export frontend_compile_python]
unsafe def frontend_compile_python
    (moduleFileName kernelFunctionName klrPythonModuleDir: String)
    (debug : UInt8) : UInt32 :=
  let d := debug != 0
  let module := moduleFileName
  let name := kernelFunctionName
  let moduleDir := klrPythonModuleDir
  let x := unsafeEIO do
      IO.FS.withTempFile fun _ tmpName => do
        gatherRun module name tmpName.toString moduleDir d
        let kernel <- KLR.File.readKLRFile tmpName .cbor
        let _ <- compilePython kernel
        return 0
  match x with
  | .ok n => n
  | .error _ => 1

@[export frontend_trace]
unsafe def frontend_trace
    (fname : String) : UInt32 :=
  let r := unsafeEIO do
    let kernel <- KLR.File.readKLRFile fname
    let kernel <- compilePython kernel
    IO.println (reprStr kernel)
    return 0
  let _ := unsafeEIO do
    match r with
    | .error e => IO.eprintln e
    | _ => .ok ()
  match r with
  | .ok rv => rv
  | .error _ => 1

@[export frontend_print]
def frontend_print : IO UInt32 := do
    IO.println ("hello")
    return 0

-- @[export frontend_print]
-- def frontend_print : UInt32 := do
--     let r := unsafeEIO do
--       IO.println ("hello")
--       return ()
--     match r with
--     | .ok rv => rv
--     | .error _ => 1
