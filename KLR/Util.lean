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

This is defined as a notation so that it can be used within mutually recursive
inductive types without issues. (abbrev introduces a new definition which
cannot be used in a mutually recursive inductive)
-/
notation "Err" => Except String

/-
The default choice for a state monad is `EStateM String`.
Again, we use a notation for the same reason as for `Err`.

Provide automatic lifting of Err, for any state monad instance.
-/
notation "StM" => EStateM String

instance : MonadLift Err (StM a) where
  monadLift
    | .ok x => .ok x
    | .error s => .error s

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
