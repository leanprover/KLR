/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.BIR.Compile.Kernel

namespace KLR.BIR

def compile (klr : Core.Kernel) : Err BIR :=
  Compile.compile_kernel klr
