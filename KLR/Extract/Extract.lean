/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import Extract.C
import Extract.Python
import Extract.Serde
import Lean

namespace Extract
open Lean Meta

private def withFile (file : String) (m : MetaM Unit) : MetaM Unit := do
  let h <- IO.FS.Handle.mk file IO.FS.Mode.write
  IO.withStdout (.ofHandle h) m

private def dirC  := "../../interop/nkic"
private def dirPy := "../../interop/klr"

run_meta do
  withFile s!"{dirC}/ast_common.h" C.generateCommonAST
  withFile s!"{dirC}/ast_python_core.h" C.generatePythonAST
  --withFile s!"{dir}/ast_python_core.py" Python.generatePythonAST
  withFile s!"{dirC}/ast_nki.h" C.generateNkiAST
  withFile s!"{dirPy}/ast_nki.py" Python.generateNkiAST
  withFile s!"{dirC}/serde_common.h" Serde.generateCommonH
  withFile s!"{dirC}/serde_common.c" Serde.generateCommonC
  withFile s!"{dirC}/serde_python_core.h" Serde.generatePythonH
  withFile s!"{dirC}/serde_python_core.c" Serde.generatePythonC
  withFile s!"{dirC}/serde_nki.h" Serde.generateNkiH
  withFile s!"{dirC}/serde_nki.c" Serde.generateNkiC
