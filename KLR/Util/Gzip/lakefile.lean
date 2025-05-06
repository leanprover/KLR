import Lake
open Lake DSL
open System(FilePath)

package Gzip where

def noStackProtector := "-fno-stack-protector"

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
      noStackProtector
    ]

def moreWeakArgs :=
  let all := #["-I", "include"]
  if System.Platform.isOSX then
    all ++ #[
      "-I", "/opt/homebrew/opt/zlib/include",
      "-I", "/usr/local/opt/zlib/include"
    ]
  else
    all ++ #[
      noStackProtector
    ]

@[default_target]
lean_lib Gzip where
  moreLinkArgs := moreLinkArgs

@[default_target]
lean_exe gzip where
  moreLinkArgs := moreLinkArgs
  root := `Main

target lean_gzip.o pkg : FilePath := do
  let oFile := pkg.buildDir / "lean_gzip.o"
  let srcJob ← inputTextFile <| pkg.dir / "lean_gzip.c"
  let ffiutil := pkg.dir / ".." / "FFIUtil" / "include"
  let weakArgs := #["-I", ffiutil.toString, "-I", (← getLeanIncludeDir).toString] ++ moreWeakArgs
  let compilerFlags := #["-fPIC", "-Werror"]
  buildO oFile srcJob weakArgs compilerFlags "cc" getLeanTrace

extern_lib liblean_gzip pkg := do
  let ffiO ← lean_gzip.o.fetch
  let name := nameToStaticLib "lean_gzip"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.19.0"

require FFIUtil from "../FFIUtil"
require Util from "../.."
