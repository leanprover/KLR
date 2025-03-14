import Lake
open Lake DSL

package "KLR" where

lean_lib "KLR" where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe "klr" where
  nativeFacets := fun _ => #[Module.oFacet]
  root := `Main

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.16.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "7a9dc3df161a437c41384bb61283410cb0911b16"
