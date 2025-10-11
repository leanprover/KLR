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

import KLR.Core
import KLR.File
import KLR.NKI
import KLR.Python
import KLR.Trace

namespace KLR.Compile
open System(FilePath)
open Lean (FromJson ToJson)
open Core (LncKernel SharedConstantFile)
open Pass (CompileResult)

private def sharedConstant
    (outfolder : String)
    (c : String × TensorLib.Tensor)
    : IO SharedConstantFile := do
  let (name, tensor) := c
  let dst := s!"{outfolder}/shared_constants"
  IO.FS.createDirAll dst
  let fName := s!"{dst}/{name}.npy"
  let data := tensor.toNpy
  data.save! (System.FilePath.mk fName)
  return ⟨name, fName⟩

structure DebugInfo where
  lnc : Nat
  ivs : Std.HashMap String (Array (Lean.Name × Int))
  stacks : Std.HashMap String (Array Lean.Name)
  deriving Lean.ToJson

private def writeDebugInfo
     (filename : String)
     (tr : List (Trace.TraceResult Unit)) : IO Unit := do
  let h <- IO.FS.Handle.mk filename IO.FS.Mode.write
  let info := (tr.zipIdx 1).map fun (res, n) => DebugInfo.mk n res.ivs res.stacks
  let json := Lean.toJson info
  h.putStr (toString json)
  h.flush

private def compile (kernel : Python.Kernel)
  : Pass.PassM (List (Trace.TraceResult Unit) × LncKernel) := do
  let kernel <- NKI.compile kernel
  let (shared, kernel) <- Trace.runLncKernels kernel
  let kernel <- Core.lowerAccessPatterns kernel
  return (shared, kernel)

-- TODO: preserve warnings and errors
def compilePython
    (kernel : Python.Kernel)
    (outfolder : Option String)
    (debugfile : Option String)
    : IO (CompileResult LncKernel) := do
  let (kernel, _warnings) := kernel.inferArguments
  let res := Pass.runPasses (compile kernel)
  match res.result with
  | none => return { res with result := none }
  | some (tr, kernel) =>
    if let some dbg := debugfile then
      writeDebugInfo dbg tr
    let cs <- match outfolder with
    | some p => tr.flatMapM fun res => res.sharedConstants.toList.mapM (sharedConstant p)
    | none => .ok []
    let kernel := { kernel with sharedConstants := cs }
    return { res with result := some kernel }

structure TensorInfo where
  name : String
  dtype : String
  shape : List Nat
  deriving ToJson

structure KernelInfo where
  name : String
  messages : List String
  warnings : List String
  errors : List String
  inputs : List TensorInfo
  outputs : List TensorInfo
  sharedConstants : List Core.SharedConstantFile
  deriving ToJson

private def resultToInfo (res : CompileResult LncKernel) : KernelInfo :=
  match res.result with
  | none => {
      name := ""
      messages := res.messages
      warnings := res.warnings
      errors := res.errors
      inputs := []
      outputs := []
      sharedConstants := []
    }
  | some kernel => {
      name := kernel.name,
      messages := res.messages
      warnings := res.warnings
      errors := res.errors
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
      sharedConstants := kernel.sharedConstants
    }

private def outfolder (outfile : String) : String :=
  let path := FilePath.mk outfile
  (path.parent.map (·.toString)).getD "."

-- reads srcPythonAstFileName, writes dstKlrFileName, returns kernel info as string of json
@[export nki_trace]
def frontend_trace (kernel : Python.Kernel) (dstKlrFileName : String) (format : String) : IO String := do
  let fmt := match format with
  | "cbor" => .cbor
  | "json" => .json
  | "sexp" => .sexp
  | _ => .cbor
  -- TODO: maybe the debug info filename should be a parameter?
  let res <- compilePython kernel (outfolder dstKlrFileName) (dstKlrFileName ++ ".debuginfo.json")
  if let some kernel := res.result then
    let f := FilePath.mk (dstKlrFileName)
    File.writeKLRFile f fmt kernel
  return toString (Lean.toJson $ resultToInfo res)

@[export nki_to_json]
def nki_to_json (kernel : Python.Kernel) : String :=
  toString (Lean.toJson kernel)

@[export klr_frontend_hello]
def frontend_hello : IO UInt32 := do
  IO.println ("hello from Lean")
  return 123

-- for testing FFI error handling when Lean code does a throw
@[export klr_frontend_throw]
def frontend_throw : IO UInt32 := do
  throw (IO.userError "frontend_throw 🙁")
  return 123

-- for testing FFI error handling when Lean code does a panic!
@[export klr_frontend_panic]
def frontend_panic : IO UInt32 := do
  panic! "frontend_panic 😵"
  return 123
