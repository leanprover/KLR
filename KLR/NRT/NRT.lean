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
