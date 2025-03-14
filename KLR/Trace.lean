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

-- Keywords recognized by the tracer (KLR keywords)
-- Limits come from:
-- https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/nki_arch_guides.html
def keywords : List (Name × Term) :=
  let ptr s memory size := (Lean.Name.mkStr1 s, Term.pointer { memory, size })
  let const s := const_var (.mkStr1 s)
  let int s := const_int (.mkStr1 s)
  [ int "arch" 2
  , const "hbm"
  , ptr "sbuf" .sbuf (128, 0x30000)
  , ptr "pmem" .pmem (128, 0x4000)
  , const "range"
  ]

def globalEnv := keywords ++ NKIEnv ++ NumpyEnv

def runNKIKernel (k : KLR.Python.Kernel) : Err (String × KLR.Core.Kernel) :=
  tracer globalEnv (traceKernel k)
