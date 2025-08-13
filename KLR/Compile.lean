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

-- reads srcPythonAstFileName, writes dstKlrFileName, returns kernel info as string of json
@[export klr_frontend_trace]
def frontend_trace (srcPythonAstFileName dstKlrFileName : String) : IO String := do
  let kernel <- KLR.File.readKLRFile srcPythonAstFileName
  let kernel <- compilePython kernel
  let f := FilePath.mk (dstKlrFileName)
  File.writeKLRFile f .cbor kernel

  -- return kernel info as JSON string
  let inputsJson := kernel.inputs.map fun inp =>
    Lean.Json.mkObj [
      ("name", Lean.toJson inp.name),
      ("dtype", Lean.toJson (reprStr inp.dtype)),
      ("shape", Lean.toJson inp.shape)
    ]

  let outputsJson := kernel.outputs.map fun out =>
    Lean.Json.mkObj [
      ("name", Lean.toJson out.name),
      ("dtype", Lean.toJson (reprStr out.dtype)),
      ("shape", Lean.toJson out.shape)
    ]

  let finalJson := Lean.Json.mkObj [
    ("name", Lean.toJson kernel.name),
    ("inputs", Lean.Json.arr inputsJson.toArray),
    ("outputs", Lean.Json.arr outputsJson.toArray)
  ]

  return toString finalJson


-- for testing basic FFI
@[export klr_frontend_hello]
def frontend_hello : IO UInt32 := do
  IO.println ("hello from Lean")
  return 0

-- for testing FFI error handling
@[export klr_frontend_fail]
def frontend_fail : IO UInt32 := do
  throw (IO.userError "frontend_fail 😵")
