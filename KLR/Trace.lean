/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Python
import KLR.Trace.Types
import KLR.Trace.Basic
import KLR.Trace.Builtin
import KLR.Trace.Python
import KLR.Trace.NKI
import KLR.Trace.Numpy

namespace KLR.Trace

def globalEnv := PythonEnv ++ NKIEnv ++ NumpyEnv

def runNKIKernel (k : KLR.Python.Kernel) : Err (String × KLR.Core.Kernel) :=
  tracer globalEnv (traceKernel k)
