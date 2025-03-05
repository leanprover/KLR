/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Trace.Types

/-
# Utilities for creating Builtins

-/

namespace KLR.Trace
open KLR.Core

namespace Builtin

def module (name : Name) : Name × Term :=
  (name, .module name)

def const_var (name: Name) : Name × Term :=
  (name, .expr (.value $ .var name.toString) (.obj name))

def const_int (name: Name) (i : Int) : Name × Term :=
  (name, .expr (.value $ .int i) .int)

abbrev BuiltinAttr := String -> Trace Term
abbrev BuiltinFn := List Term -> List (String × Term) -> Trace Term

/-
Fetch the (Python) arguments given in `pos` and `kw` according to the
specification in `names`. If an argument is not present, a default may be
specified. If no default is available, throw an error.
-/
def getArgs (names : List (String × Option a))
            (pos : List a) (kw : List (String × a))
            : Err (List a) := do
  let extra := names.drop pos.length
  let kws <- extra.mapM fun (name, dflt) => do
    match kw.find? (fun p => p.fst == name) with
    | some x => return x.snd
    | none => match dflt with
              | some x => return x
              | none => throw s!"argument {name} not found"
  return pos.append kws

-- Convert Python arguments to an order list of terms and call function.
def withArgs [Monad m] [MonadExcept String m] [MonadLift Err m]
             (names : List (String × Option a)) (f : List a -> m b)
             (args : List a) (kwargs : List (String × a)) : m b :=
    do f (<- getArgs names args kwargs)
