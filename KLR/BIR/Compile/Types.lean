/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.BIR.Instruction
import KLR.BIR.Instructions
import KLR.BIR.Function
import KLR.Core
import KLR.Util

namespace KLR.BIR.Compile

-- Introduce a Compile monad, in case we need something more in the future.
abbrev Compile := Err
