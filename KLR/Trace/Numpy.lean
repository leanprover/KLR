/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin

/-
# Numpy built-ins
-/
namespace KLR.Trace

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

def NumpyEnv : List (Name × Term) :=
  module numpy :: syms.map fun s => const_var (np s)
