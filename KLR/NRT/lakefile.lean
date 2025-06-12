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
  "https://github.com/leanprover/lean4-cli.git" @ "v4.20.0"

require FFIUtil from "../Util/FFIUtil"
