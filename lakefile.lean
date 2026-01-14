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
open Lake DSL

package "KLR" where

@[default_target]
lean_lib "KLR" where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib "Extract" where
  srcDir := "KLR/Extract"

@[default_target]
lean_exe "klr" where
  nativeFacets := fun _ => #[Module.oFacet]
  root := `Main
  supportInterpreter := true

lean_exe "klr-fuzz" where
  root := `KLR.Fuzz.Main
  supportInterpreter := true

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.23.0"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.23.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.16"

require SHerLOC from git
  "https://github.com/leanprover/SHerLOC.git" @ "c74ae090d4326cca9ff636184c330a67ca039ef6"

-- Comment the above and uncomment this for local development
-- require TensorLib from "../TensorLib"

--require iris from git
--  "https://github.com/markusdemedeiros/iris-lean.git"
