/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import ISA.Basic

/-
# Code to simplify parsed ISA specifications.

Note, more is needed, this is just a starting point.
-/

namespace ISA.Simplify

structure State where
  isa : ISA := {}
  nameMap : RBMap Name Name compare := ∅

abbrev Simp := StM State

def lookup (name : Name) : Simp Expr := do
  let st <- get
  match st.isa.consts.find? name.toString with
  | some x => return .int x
  | none => return .var (st.nameMap.findD name name)

def binop (op : BinOp) (l r : Int) : Int :=
  match op with
  | .multiply => l * r
  | .divide => l / r
  | .shiftLeft => l.toNat <<< r.toNat
  | po => panic! s!"unimp {repr po}"

def simplifyExpr : Expr -> Simp Expr
  | .int i => return .int i
  | .var v => lookup v
  | .cast e t s => return .cast (<- simplifyExpr e) t s
  | .proj l r => return .proj (<- simplifyExpr l) (<- simplifyExpr r)
  | .index l r => return .index (<- simplifyExpr l) (<- simplifyExpr r)
  | .unop op e => return .unop op (<- simplifyExpr e)
  | .binop op l r => do
    match <- simplifyExpr l, <- simplifyExpr r with
    | .int l, .int r => return .int (binop op l r)
    | l , r => return .binop op l r
  | .cmp op l r => return .cmp op (<- simplifyExpr l) (<- simplifyExpr r)
  | .cond c t e => return .cond (<- simplifyExpr c) (<- simplifyExpr t) (<- simplifyExpr e)
  | .call f args => return .call f (<- args.attach.mapM fun ⟨ x, _ ⟩ => simplifyExpr x)

def simplifyFunction (f : Function) : Simp Function := do
  return { f with expr := <- simplifyExpr f.expr }

def simplifyChecks (fmt : InstFormat) : Simp InstFormat := do
  let mut checks : Env Function := ∅
  for (n, f) in fmt.checks do
    let f <- simplifyFunction f
    checks := checks.insert n f
  return { fmt with checks }


-- Simplify structure fields
def field : String -> Typ -> Err (Option (String × Typ))
  | "header", .named "Header" => return some ("opcode", .named "Opcode")
  | name, .named "Header" => throw s!"Header is called {name} (not header)"
  | "events", .named "Events" => return none
  | name, .named "Events" => throw s!"Events is called {name} (not events)"
  | "reserved0", _ => return none
  | name, t => return some (name, t)

def struct (es : List (String × Typ)) : Err (List (String × Typ)) := do
  let mut result := []
  for (n, t) in es do
    if let some (n,t) := <- field n t then
      result := (n,t) :: result
  return result.reverse

def simplifyFields (fmt : InstFormat) : Simp InstFormat := do
  let fields <- struct fmt.fields
  return { fmt with fields }

-- Instructions are mostly spelled the same as their opcodes, but not always
-- There is no explicit mapping in the ISA specification
private def instToOpcode : String -> String
  | "DMATranspose" => "DmaTranspose"
  | "PseudoGIDLoad" => "PseudoGidLoad"
  | "ScalarTensorTensorArithOp" => "ScalarTensorTensorArith"
  | "ScalarTensorTensorBitvecOp" => "ScalarTensorTensorBitvec"
  | s => s

-- An instruction may be missing, but to distinguish between misspellings
-- and missing we keep a list of opcodes that may be missing
private def mayBeMissing : List String := [
  "TensorScalarPtrMultiDualArith",
  "TensorScalarPtrMultiDualBitvec",
  ]

-- Lookup an opcode, check for misspellings, missing, or deprecated
private def lookupOpcode (isa : ISA) (inst : String) : Err (Option String) :=
  let opc := instToOpcode inst
  match isa.opcodes.lookup opc with
  | .ok true => return (some opc)
  | .ok false => return none
  | .error s =>
      if mayBeMissing.contains opc then
        return none
      else .error s

def simplifyOpcodes (fmt : InstFormat) : Simp InstFormat := do
  let isa := (<- get).isa
  match <- isa.items.lookup fmt.name with
  | .struct _ fields => do
    let mut opcodes := []
    for op in fmt.opcodes do
      if let some op := <- lookupOpcode isa op then
        opcodes := op :: opcodes
    return { fmt with opcodes, fields }
  | _ => throw s!"structure {fmt.name} not found"

def simplifyISA : Simp ISA := do
  let isa := (<- get).isa
  let mut insts : Env InstFormat := ∅
  for (n, i) in isa.insts do
    let i <- simplifyOpcodes i
    let i <- simplifyFields i
    let i <- simplifyChecks i
    insts := insts.insert n i
  return { isa with insts }

def simplify (isa : ISA) : Err ISA := do
  match simplifyISA { isa } with
  | .ok isa _ => return isa
  | .error s _ => throw s
