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

def moreLinkArgs :=
  let all := #["-lz"]
  if System.Platform.isOSX then
    all ++ #[
      "-L/opt/homebrew/opt/zlib/lib",
      "-L/usr/local/opt/zlib/lib"
    ]
  else
    -- TODO: figure out how to properly compile/link with ssp turned on
    all ++ #[
      "-fno-stack-protector"
    ]

@[default_target]
lean_lib "KLR" where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe "klr" where
  nativeFacets := fun _ => #[Module.oFacet]
  root := `Main
  moreLinkArgs := moreLinkArgs
  supportInterpreter := true

require Archive from "KLR/Util/Archive"

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.21.0"

require Gzip from "KLR/Util/Gzip"

require NRT from "KLR/NRT"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.21.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.13"

-- Comment the above and uncomment this for local development
-- require TensorLib from "../TensorLib"

require Util from "KLR"
