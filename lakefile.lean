import Lake
open Lake DSL

package "KLR" where

lean_lib "KLR" where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib "ISA" where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe "klr" where
  nativeFacets := fun _ => #[Module.oFacet]
  root := `Main

lean_exe "isagen" where
  nativeFacets := fun _ => #[Module.oFacet]
  root := `IsaGen

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.17.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.4"

-- Comment the above and uncomment this for local development
-- require TensorLib from "../TensorLib"
