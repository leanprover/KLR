import Lake
open Lake DSL

package "KLR" where

lean_lib "KLR" where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe "klr" where
  defaultFacets := #[LeanLib.staticFacet]
  root := `Main

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.16.0"
