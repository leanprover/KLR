/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Util
import KLR.NKI.Basic
import KLR.Semantics.NML
import KLR.Semantics.Memory

/- # Semantics for NKI by translation to NML

TODO: At the moment, it fixes DataT to float. Not sure the best way to
add different data interpretations from the frontend.
-/

open KLR


/- Model of a NKI Program in NML -/
structure NKIModel where
  name : String
  file : String
  body : List (NML.Stmt Float)

def KLR.NKI.Value.model (s : NKI.Value) : Err (NML.Value Float) :=
  match s with
  | .none => .ok .unit
  | .bool b => .ok <| .bool b
  | .int z => .ok <| .int z
  | .float f => .ok <| .data f
  | .string _ => .error "string values not added"
  | .tensor _ _ _ => .error "tensor values not added" -- TODO: I think this is a ptr

def KLR.NKI.Expr.model (s : NKI.Expr) : Err (NML.Expr Float) :=
  match s.expr with
  | .value v => match v.model with | .error s => .error s | .ok e' => .ok <| .val e'
  | .var n => .ok <| .var n.toString
  | .tuple _ => .error "tuples not modeled"
  | .access _ _ => .error "access not modeled"
  | .binOp _ _ _ => .error "binop not modeled"
  | .conj _ _ => .error "conj not modeled"
  | .disj _ _ => .error "disj not modeled"
  | .ifExp _ _ _ => .error "ifExp not modeled"
  | .call _ _ _ => .error "call not modeled"

def KLR.NKI.Stmt.model (s : NKI.Stmt) : Err (NML.Stmt Float) :=
  match s.stmt with
  | .expr e => match e.model with | .error s => .error s | .ok e' => .ok <| .assign none e'
  | .assert _ => .error ".assert statement not modeled"
  | .ret e => match e.model with | .error s => .error s | .ok e' => .ok <| .ret e'
  | .declare _ _ => .error ".declare statement not modeled"
  | .letM x _ e =>
      match e.model with
      | .error s => .error s
      | .ok e' =>
      match x with
      | .tuple _ => .error "letM .tuple patterns not modeled"
      | .var n => .ok <| .assign (.some n.toString) e'
  | .setM _ _ _ => .error ".setM statement not modeled"
  | .ifStm _ _ _ => .error ".ifStm statement not modeled"
  | .forLoop _ _ _ => .error ".forLoop statement not modeled"
  | .breakLoop => .error ".breakLoop statement not modeled"
  | .continueLoop => .error ".continueLoop statement not modeled"

def NKI.model (k : NKI.Kernel) : Err NKIModel :=
  -- Why doesn't monad syntax work in this line? Universe issue
  match k.funs with
  | [f] =>
    match f.body.mapM KLR.NKI.Stmt.model with
    | .error s => .error s
    | .ok b => .ok { name := f.name, file := f.file, body := b}
  | _ => .error "multiple funs not supported"


def NML.Value.pprint : NML.Value Float → String
| .unit => ".unit"
| .bool b => s!".bool {b}"
| .int z => s!".int {z}"
| .data f => s!".data {f}"
| _ => "{NML.Value.pprint: Not implemented}"

-- | ptr      (p : TensorHandle)
-- /-- [ uptr ] A raw reference to a chip in memory -/
-- | uptr     (i : ChipIndex)
-- /-- [ iptr ] A raw reference to a location inside a chip's memory -/
-- | iptr     (i : Nat × Nat)
-- /-- [ iref ] A reference to an iterator value.
-- We give all of our iterators explicit names so that proof rules can represent
-- relationships between them. -/
-- | iref     (i : Nat)
-- /-- [ lidx ] A logical index into a tensor. -/
-- | lidx     (l : List Int)


def NML.Expr.pprint : NML.Expr Float → String
| .val v => s!".val ({v.pprint})"
| .var x => s!".var \"{x}\""
| _ => "{NML.Expr.pprint: Not implemented}"

-- /-- [ var ] Variable reference. -/
-- | var           (x : String)
-- /-- [ dunop ] Apply a unary function to a piece of data. -/
-- | dunop         (e : Expr) (f : DataT → DataT)
-- /-- [ alloc ] Nonphysical tensor allocation.
-- Generate a new, empty, nonphysical tensor block inside the given memory. -/
-- | alloc         (m : Memory)
-- /-- [ readp ] Raw point read.
-- Access the data stored in a given chip at a given index. This read is "raw"
-- in the sense that it does not perform any layout calculations. -/
-- | readp         (chip index : Expr)
-- /-- [ idx ] A list of expressions, that should be thought of as reducing to a single logical address. -/
-- | idx           (l : List Expr)
-- /-- [ chip ] Access the chip (uptr) from the metadata of a ptr -/
-- | chip          (ptr : Expr)
-- /-- [ ix ] Compute the raw location (iptr) of an address given a logical address. -/
-- | ix            (ptr : Expr) (index : Expr)



def NML.Stmt.pprint : NML.Stmt Float → String
| .ret e => s!".ret ({e.pprint})"
| .assign none e => s!".assign none ({e.pprint})"
| .assign (.some x) e => s!".assign (some \"{x}\") ({e.pprint})"
| _ => "{NML.Stmt.pprint: Not implemented}"

-- iterators be values) to avoid difficult cases such as iterators of iterators. -/
-- | mkiter       (n : Nat) (i : Iterator DataT)
-- /-- [ frame ] (Internal) Evaluate a list of statements with a given local context. -/
-- | frame        (p : List Stmt) (ctx : LocalContext DataT)
-- /-- [ loop ] Looping construct. The argument should evaluate to a iterator variable. -/
-- | loop         (x : String) (it : Expr DataT) (body : List Stmt)
-- /-- [ setp ] Set a single memory location -/
-- | setp         (chip index val : @Expr DataT)

/-- Print out a string representation of the NKI program -/
def NKI.pprint (p : NKIModel) : String :=
  s!"
-- generated from {p.file}
def {p.name} : NML.ExecState Float :=
  .run
  [ {"\n    ".intercalate <| .map (· ++ ",") <| p.body.map NML.Stmt.pprint}
  ]
  (LocalContext.emp Float)
"
