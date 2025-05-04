import Lake
open Lake DSL System

package NRT where

@[default_target]
lean_lib NRT

@[default_target]
lean_exe nrt where
  moreLinkArgs := #["-L/opt/aws/neuron/lib", "-lnrt"]
  root := `Main

target leannrt.o pkg : FilePath := do
  let oFile := pkg.buildDir / "leannrt.o"
  let srcJob ← inputTextFile <| pkg.dir / "leannrt.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", "/opt/aws/neuron/include"] -- TODO: better way to find neuron path
  buildO oFile srcJob weakArgs #["-std=c11", "-fPIC", "-Werror"] "cc" getLeanTrace

extern_lib libleannrt pkg := do
  let ffiO ← leannrt.o.fetch
  let name := nameToStaticLib "leannrt"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.19.0"
