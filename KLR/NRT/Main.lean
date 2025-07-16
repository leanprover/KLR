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
import NRT

open Cli

def impossible {a : Type} [h : Inhabited a] (msg : String := "") :=
  @panic a h s!"Invariant violation: {msg}"

def runNeff (p : Parsed) : IO UInt32 := do
  let neff := p.positionalArg! "neffFile" |>.as! String
  let inputs := p.variableArgsAs! String
  if inputs.size % 2 != 0 then throw $ IO.userError "inputs must be in pairs name/file" else
  let rec split (xs : List String) : IO (List NRT.TensorFile) := match xs with
  | [] => return []
  | name :: path :: rest => do
    let fps <- split rest
    if ! (<- System.FilePath.pathExists path) then
      throw $ IO.userError s!"Path {path} doesn't exist"
    else if name.contains '.' || name.contains '/' then
      throw $ IO.userError s!"Name {name} shouldn't contain path-like symbols like '.' or '/'"
    else
      return NRT.TensorFile.mk name path :: fps
  | [_] => impossible
  let inputs <- split inputs.toList
  let mut res <- NRT.execute neff inputs.toArray
  if p.hasFlag "outdir" then
    let dir := p.flag! "outdir" |>.as! String
    let dir := System.mkFilePath (dir.splitOn "/")
    let dir <- IO.FS.realPath dir
    for tf in res do
      let old <- IO.FS.realPath tf.filePath
      let new := dir / tf.fileName
      IO.println s!"Moving {old} to {new}"
      try
        IO.FS.rename old new
        res := res.map fun tf => tf.withOutputDir dir
      catch _ =>
        IO.println "Cannot rename the output files. Is the directory on a different mount point?"
        IO.println "If so, you will need to move the files manually for now. Sorry!"
  IO.println s!"Generated outputs: {res}"
  return 0

def runNeffCmd := `[Cli|
  "run-neff" VIA runNeff;
  "Run a NEFF file on named input tensors."

  FLAGS:
    d, outdir : String; "Output directory for output tensor files. (Default is cwd)"

  ARGS:
    neffFile : String; "NEFF file"
    ...inputFiles : String; "Pairs of names and input files corresponding to the tensor inputs in the NEFF." ++
                            "For example, run-neff /tmp/foo.neff a_tensor /tmp/a.tensor b_tensor /var/b.tensor" ++
                            "would map `a_tensor` which is expected by the NEFF to the bytes in `/tmp/a.tensor`, etc." ++
                            "Currently only files of bytes are supported. NumPy format (.npy) files seem supported by " ++
                            "the runtime, but we haven't got them to work yet. You can generate bytes from an ndarray by calling " ++
                            "    with open('a_tensor', 'wb') as f:" ++
                            "        arr.tofile(f)"
]

def runTests (_ : Parsed) : IO UInt32 := do
  IO.println "Running Lean tests..."
  return 0

def runTestsCmd := `[Cli|
  "test" VIA runTests;
  "Run tests"
]

def nrtCmd : Cmd := `[Cli|
  nrt NOOP; ["0.0.1"]
  "Lean code that works with the Neuron Runtime (NRT)"

  SUBCOMMANDS:
    runNeffCmd;
    runTestsCmd
]

def main (args : List String) : IO UInt32 :=
  if args.isEmpty then do
    IO.println nrtCmd.help
    return 0
  else do
   nrtCmd.validate args
