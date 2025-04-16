/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

/-
NRT API:  https://awsdocs-neuron.readthedocs-hosted.com/en/latest/neuron-runtime/nrt-api-guide.html#the-model-api
-/
open System(FilePath)

namespace NRT

structure TensorFile where
  tensorName : String
  filePathString : String
deriving BEq, Repr

namespace TensorFile

def filePath (f : TensorFile) : FilePath :=
  let parts := f.filePathString.splitOn "/"
  let parts := if parts.length == 1 then "." :: parts else parts
  System.mkFilePath parts

def fileName (f : TensorFile) : FilePath := f.filePath.fileName.getD ""

def withOutputDir (f : TensorFile) (p : FilePath) : TensorFile :=
  let path := f.filePath
  let name := path.fileName.getD ""
  let path := p / name
  { f with filePathString := path.toString }

#guard (TensorFile.mk "c_tensor" "a/b/c.bin").withOutputDir "/tmp" == TensorFile.mk "c_tensor" "/tmp/c.bin"

end TensorFile

instance : ToString TensorFile where
  toString x := reprStr x

@[extern "lean_nrt_execute"]
opaque execute (neffFileName : @&String) (inputTensorfiles : @&Array @&TensorFile) : IO (Array TensorFile)

end NRT
