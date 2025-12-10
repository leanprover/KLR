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
  info : Array Trace.DebugItem
  deriving Lean.ToJson

private def writeDebugInfo
     (filename : String)
     (tr : List (Trace.TraceResult Unit)) : IO Unit := do
  let h <- IO.FS.Handle.mk filename IO.FS.Mode.write
  let info := (tr.zipIdx 1).map fun (res, n) => DebugInfo.mk n res.debug
  let json := Lean.toJson info
  h.putStr (toString json)
  h.flush

private def writeMessagesFile
  (filename: String)
  (suffix: String)
  (messages: Array String) : IO String := do
  let dst := filename ++ "_" ++ suffix
  let h <- IO.FS.Handle.mk dst IO.FS.Mode.write
  _ <- messages.mapM h.putStrLn
  h.flush
  return dst

private def compile (kernel : Python.Kernel) (genDebug : Bool := false)
  : Pass.PassM (List (Trace.TraceResult Unit) × LncKernel) := do
  let kernel <- NKI.compile kernel
  let unsafeCast := match kernel.flags.find? (·.1 == "UNSAFE_FP8FNCAST") |>.map (·.2) with
    | some $ .bool b => b
    | _ => false
  let (shared, kernel) <- Trace.runLncKernels kernel genDebug
  let (kernel, _) <- Core.lowerAccessPatterns kernel { unsafeCast := unsafeCast }
  let convertTensor (t : Core.TensorName) : Option Core.TensorName :=
    if t.dtype == .float8_e4m3fn then
      Core.TensorName.make t.name .float8_e4m3 t.shape t.address t.addressRotation |>.toOption
    else some t
  let kernel := if unsafeCast then
    { kernel with
      inputs := kernel.inputs.filterMap convertTensor,
      outputs := kernel.outputs.filterMap convertTensor
    }
  else kernel
  return (shared, kernel)

-- TODO: preserve warnings and errors
def compilePython
    (kernel : Python.Kernel)
    (outfolder : Option String)
    (debugFile : Option String)
    : IO (CompileResult LncKernel) := do
  let (kernel, _warnings) := kernel.inferArguments
  let res := Pass.runPasses (compile kernel debugFile.isSome)
  match res.result with
  | none => return { res with result := none }
  | some (tr, kernel) =>
    if let some dbg := debugFile then
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
  messages : String
  warnings : String
  errors : String
  inputs : List TensorInfo
  outputs : List TensorInfo
  sharedConstants : List Core.SharedConstantFile
  sharedBuffers : List TensorInfo
  deriving ToJson

private def resultToInfo (res : CompileResult LncKernel) (msgsFile errorsFile warningsFile: String) : KernelInfo :=
  match res.result with
  | none => {
      name := ""
      messages := msgsFile
      warnings := warningsFile
      errors := errorsFile
      inputs := []
      outputs := []
      sharedConstants := []
      sharedBuffers := []
    }
  | some kernel => {
      name := kernel.name,
      messages := msgsFile
      warnings := warningsFile
      errors := errorsFile
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
      sharedBuffers := kernel.sharedBuffers.map fun buf => {
        name := buf.name,
        dtype := reprStr buf.dtype,
        shape := buf.shape.toList
      }
    }

private def outfolder (outfile : String) : String :=
  let path := FilePath.mk outfile
  (path.parent.map (·.toString)).getD "."

-- reads srcPythonAstFileName, writes dstKlrFileName, returns kernel info as string of json
@[export nki_trace]
def frontend_trace
    (kernel : Python.Kernel)
    (dstKlrFileName : String)
    (format : String)
    (dbgFileName : Option String)
    : IO String := do
  let fmt := match format with
  | "cbor" => .cbor
  | "json" => .json
  | "sexp" => .sexp
  | _ => .cbor
  -- TODO: maybe the debug info filename should be a parameter?
  let outfolder := outfolder dstKlrFileName
  let res <- compilePython kernel outfolder dbgFileName
  if let some kernel := res.result then
    let f := FilePath.mk (dstKlrFileName)
    File.writeKLRFile f fmt kernel
  let msgsFile <- writeMessagesFile (outfolder ++ "/" ++ kernel.entry) "messages" res.messages
  let errsFile <- writeMessagesFile (outfolder ++ "/" ++ kernel.entry) "errors" res.errors
  let warnsFile <- writeMessagesFile (outfolder ++ "/" ++ kernel.entry) "warnings" res.warnings
  return toString (Lean.toJson $ resultToInfo res msgsFile errsFile warnsFile)

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
