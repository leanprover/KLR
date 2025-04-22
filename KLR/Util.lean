/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import KLR.Util.Base64
import KLR.Util.SHA256

namespace KLR

/-
The default choice for an error monad is `Except String`, used for simple
computations that can fail.

Provide automatic lifting of Err to any monad that supports throwing strings
as errors.
-/
abbrev Err := Except String

instance [Monad m] [MonadExcept String m] : MonadLift Err m where
  monadLift
    | .ok x => return x
    | .error s => throw s

/-
The default choice for a state monad is `EStateM String`.
-/
abbrev StM := EStateM String

def impossible {a : Type} [h : Inhabited a] (msg : String := "") :=
  @panic a h s!"Invariant violation: {msg}"

def get! [Inhabited a] (x : Err a) : a := match x with
| .error msg => impossible msg
| .ok x => x

def natDivCeil (num denom : Nat) : Nat := (num + denom - 1) / denom
