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

import Lake
open Lake DSL System

package NRT where

target leannrt.o pkg : FilePath := do
  let oFile := pkg.buildDir / "leannrt.o"
  let srcJob ← inputTextFile <| pkg.dir / "leannrt.c"
  let ffiutil := pkg.dir / ".." / "Util" / "FFIUtil" / "include"
  let weakArgs := #["-I", ffiutil.toString, "-I", (← getLeanIncludeDir).toString, "-I", "/opt/aws/neuron/include"] -- TODO: better way to find neuron path
  buildO oFile srcJob weakArgs #["-std=c11", "-fPIC", "-Werror"] "cc" getLeanTrace

target libleannrt pkg : FilePath := do
  let ffiO ← leannrt.o.fetch
  let name := nameToStaticLib "leannrt"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

@[default_target]
lean_lib NRT where
  moreLinkObjs := #[libleannrt]

@[default_target]
lean_exe nrt where
  moreLinkArgs := #["-L/opt/aws/neuron/lib", "-lnrt"]
  root := `Main

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.22.0"

require FFIUtil from "../Util/FFIUtil"
