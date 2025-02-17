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

-- We are only using numpy to name operators
-- This will be changed in upcoming NKI API and we will not need this.
private def syms := [
  "uint8" , "int8" , "uint16" , "int16" , "uint32" , "int32" , "float16" , "float32" , "bool",
  "bitwise_not", "bitwise_invert", "bitwise_and", "bitwise_or", "bitwise_xor",
  "bitwise_left_shift", "bitwise_right_shift",
  "add", "subtract", "multiply", "maximum", "minimum",
  "equal", "not_equal", "greater_equal", "greater", "less_equal", "less",
  "logical_not", "logical_and", "logical_or", "logical_xor"
  ]

def NumpyEnv : List (Name × Item) :=
  module numpy :: syms.map fun s => const_var (np s)
