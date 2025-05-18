/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import Lake
open Lake DSL
open System(FilePath)

package Archive

def noStackProtector := "-fno-stack-protector"

def moreLinkArgs :=
  let all := #["-larchive"]
  if System.Platform.isOSX then
    all ++ #[
      "-L/opt/homebrew/opt/libarchive/lib",
      "-L/usr/local/opt/libarchive/lib"
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
      "-I", "/opt/homebrew/opt/libarchive/include",
      "-I", "/usr/local/opt/libarchive/include"
    ]
  else
    all ++ #[
      noStackProtector
    ]

@[default_target]
lean_lib Archive where
  moreLinkArgs := moreLinkArgs

@[default_target]
lean_exe archive where
  moreLinkArgs := moreLinkArgs
  root := `Main

target lean_archive.o pkg : FilePath := do
  let oFile := pkg.buildDir / "lean_archive.o"
  let srcJob ← inputTextFile <| pkg.dir / "lean_archive.c"
  let ffiutil := pkg.dir / ".." / "FFIUtil" / "include"
  let weakArgs := #["-I", ffiutil.toString, "-I", (← getLeanIncludeDir).toString] ++ moreWeakArgs
  let compilerFlags := #["-fPIC", "-Werror"]
  buildO oFile srcJob weakArgs compilerFlags "cc" getLeanTrace

extern_lib liblean_archive pkg := do
  let ffiO ← lean_archive.o.fetch
  let name := nameToStaticLib "lean_archive"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.19.0"

require FFIUtil from "../FFIUtil"
