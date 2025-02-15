/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin

/-
# Numpy built-ins
-/
namespace KLR.Trace
open KLR.Trace.Builtin

private def numpy : Name := .str .anonymous "numpy"
private def np : String -> Name := .str numpy

def NumpyEnv : List (Name × Item) :=
  [ module numpy
  ]
