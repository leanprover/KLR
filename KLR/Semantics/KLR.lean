/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.NML

/- # Semantics for KLR by translation to NML -/

open KLR.Core

variable (DataT : Type _)
variable (float_interp : Float → KLR.Err DataT)

def KLR.Core.Value.semantics (s : KLR.Core.Value) : Err (@NML.Value DataT) :=
  match s with
  | bool b => .ok <| .bool b
  | int i => .ok <| .int i
  | float f => (float_interp f).map .data
  -- | access (a : Access)
  | _ => .error "Semantics not defined"
  -- Variables. Why does KLR call these a value??


def KLR.Core.Stmt.semantics (DataT : Type _) (s : KLR.Core.Stmt) : Err (@NML.Stmt DataT) :=
  match s with
  | .ret v => .ok <| .ret sorry
  | _ => .error "Semantics not defined"
