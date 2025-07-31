/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Lean
import KLR.Semantics.NML

open Lean Elab Meta

elab "#debug_expr " termStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let s ← elabTerm termStx (expectedType? := none)
      logInfo s!"elaboration: {s}"
    catch | _ => throwError s!"failure"

#debug_expr @NML.Locals.bind


/-## NML Values -/
declare_syntax_cat nml_val
syntax "%u "      : nml_val
syntax "%b " term : nml_val
syntax "%d " term : nml_val
syntax "%i " term : nml_val
syntax "%a " term : nml_val
syntax "%p " term : nml_val
syntax "%s " term : nml_val

syntax "[nml_val|" nml_val "]" : term

macro_rules
| `([nml_val| %u])    => `(@NML.Value.unit _)
| `([nml_val| %b $b]) => `(@NML.Value.bool _ $b)


-- #check [nml_val| %u ]
-- #check [nml_val| %b true ]

declare_syntax_cat nml_binding
syntax term " ↣ " nml_val : nml_binding
syntax "[nml_binding|" nml_binding "]" : term
macro_rules
| `([nml_binding| $x:term ↣ $y:nml_val]) => `(fun l => @NML.Locals.bind _ l $x [nml_val| $y])
-- #check  [nml_binding| "x" ↣ %b true]

declare_syntax_cat nml_locals

elab "[nml_locs|" tuples:nml_binding,* "]" : term => do
  let mut _ : Expr := Expr.const ``NML.nolocals []
  for tup in tuples.getElems do
    match tup with
    | `(nml_binding| $p:term ↣ $v) => logInfo s!"OK {p} and {v}"
    | stx => throwError s!"{stx}"
  return Expr.const ``Unit.unit []
  -- return b

-- #check ([nml_locs| "x" ↣ %b true, "y" ↣ %u])
-- #eval Lean.Meta.reduce `(NML.nolocals _)
