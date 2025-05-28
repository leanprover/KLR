/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.BIR.Compile.Types
import KLR.Core

namespace KLR.BIR.Compile
open KLR.Core

class ToInst (a : Type) where
  toInst : a -> Compile Inst
open ToInst(toInst)

-- Note: it may be easier to just define the ToJson methods
-- of the Operators to output BIR-valid json, and eliminate the
-- Instructions alltogether.

instance : ToInst Core.TensorScalar where
  toInst ts := return .TensorScalar {
    op0 := ts.op0
    const0 := ts.const0.toFloat
    reverse0 := ts.reverse0
    op1 := ts.op1
    const1 := ts.const1.toFloat
    reverse1 := ts.reverse1
  }

instance : ToInst Core.TensorScalarAddr where
  toInst ts := return .TensorScalarPtr {
    op0 := ts.op0
    reverse0 := ts.reverse0
    op1 := ts.op1
    reverse1 := ts.reverse1
    is_tensor_scalar_addr := some true
  }

def translateOperator : Operator -> Compile Inst
  | .load => return .Load { }
  | .save => return .Save { }
  | .const => throw "translateOperator: unimplemented: .const"
  | .tensorScalar ts => toInst ts
  | .tensorScalarAddr ts => toInst ts
