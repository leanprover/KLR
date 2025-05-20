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
  "https://github.com/leanprover/lean4-cli.git" @ "v4.19.0"

require Gzip from "KLR/Util/Gzip"

require NRT from "KLR/NRT"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.19.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.9"

-- Comment the above and uncomment this for local development
-- require TensorLib from "../TensorLib"

require Util from "KLR"
