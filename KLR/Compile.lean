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
open Lean (FromJson ToJson)

def eprintln [ToString a] (debug : Bool) (x : a) : IO Unit := do
  if debug then IO.eprintln x

private def sharedConstant (outfolder : String) (c : String × TensorLib.Tensor) : IO (String × String) := do
  let (name, tensor) := c
  let dst := s!"{outfolder}/shared_constants"
  IO.FS.createDirAll dst
  let fName := s!"{dst}/{name}.npy"
  let data := tensor.toNpy
  data.save! (System.FilePath.mk fName)
  return (name, fName)

-- TODO: preserve warnings and errors
def compilePython (kernel : Python.Kernel) (outfolder : Option String) : IO Core.LncKernel := do
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
  let (warnings, kernels, sharedConstants) <- KLR.Trace.runLncKernels kernel
  if !warnings.isEmpty then
    IO.eprintln warnings
  let cs <- match outfolder with
  | some p => sharedConstants.mapM (fun c => sharedConstant p c)
  | none => .ok #[]
  let kernels <- Core.lowerAccessPatterns kernels
  return {kernels with sharedConstants := (cs.map fun (name, fileName) => {name := name, fileName := fileName}).toList}

structure TensorInfo where
  name : String
  dtype : String
  shape : List Nat
  deriving ToJson

structure KernelInfo where
  name : String
  inputs : List TensorInfo
  outputs : List TensorInfo
  deriving ToJson

-- reads srcPythonAstFileName, writes dstKlrFileName, returns kernel info as string of json
@[export klr_frontend_trace]
def frontend_trace (srcPythonAstFileName dstKlrFileName : String) : IO String := do
  let kernel <- KLR.File.readKLRFile srcPythonAstFileName
  let kernel <- compilePython kernel none
  let f := FilePath.mk (dstKlrFileName)
  File.writeKLRFile f .cbor kernel

  let kernelInfo : KernelInfo := {
    name := kernel.name,
    inputs := kernel.inputs.map fun inp => {
      name := inp.name,
      dtype := reprStr inp.dtype,
      shape := inp.shape.toList
    },
    outputs := kernel.outputs.map fun out => {
      name := out.name,
      dtype := reprStr out.dtype,
      shape := out.shape.toList
    },
  }
  return toString (Lean.toJson kernelInfo)

-- for testing basic FFI
@[export klr_frontend_hello]
def frontend_hello : IO UInt32 := do
  IO.println ("hello from Lean")
  return 0

-- for testing FFI error handling
@[export klr_frontend_fail]
def frontend_fail : IO UInt32 := do
  throw (IO.userError "frontend_fail 😵")
