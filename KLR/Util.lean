/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

-- Common Utilities

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

/-
A common issue is failure to prove termination automatically when using
List.mapM. There is a work-around for this which involves introducing
`{ x // x ∈ l }` in place of the list `l`.

We can capture this trick in a notation. Note we need to use a notation and not
a definition because the proof object `x∈l` needs to be available to the
termination proof tactics, in the scope of the original function.

Writing, `List.mapM f l`, as `f ▷ l` doesn't break the termination proof.
Note: ▷ is typed as \rhd
-/
notation f "▷" l =>
  List.mapM (fun ⟨ x, _ ⟩ => f x) (List.attach l)

def impossible {a : Type} [h : Inhabited a] (msg : String := "") :=
  @panic a h s!"Invariant violation: {msg}"
