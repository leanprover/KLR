/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Util
import KLR.NKI.Basic
import KLR.Semantics.NML
import KLR.Semantics.Memory

/- # Semantics for NKI by translation to NML

TODO: This should really be a metaprogram: I want it to return an expression representing
a NML program rather than a NML program itself. This is so I can pretty print eg. the values
of iterators (Lean terms) and don't need to fix DataT upfront. -/

open KLR Lean NML


structure NKIModelCtx where
  fresh_it : Nat

def NKIModelCtx.it_inc (c : NKIModelCtx) : NKIModelCtx :=
  { c with fresh_it := c.fresh_it + 1 }

def NKIModelCtx.default : NKIModelCtx where
  fresh_it := 0


/-- Model the program where DataT is Float. -/
structure NMLModel where
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


-- TODO: Add Iterator expression steps to the model.
-- Right now, all iterator expressions must be static.
def KLR.NKI.iterator.model : Iterator → Err NML.IteratorS
  | .expr _ => .error ".expr iterators no modeled"
  | .range _ l u s =>
      match KLR.NKI.Expr.model l with
      | .error s => .error s
      | .ok (.val <| .int zl) =>
        match KLR.NKI.Expr.model u with
        | .error s => .error s
        | .ok (.val <| .int zu) =>
          match KLR.NKI.Expr.model s with
          | .error s => .error s
          | .ok (.val <| .int zs) =>
            .ok <| IteratorS.affineRange zl zu zs
          | _ => .error "Not modeled: dynamic loop bound s"
        | _ => .error "Not modeled: dynamic loop bound u"
      | _ => .error "Not modeled: dynamic loop bound l"

-- TODO: Cleanup
partial def KLR.NKI.Stmt.model (c : NKIModelCtx) (s : NKI.Stmt) : Err (NKIModelCtx × List (NML.Stmt Float)) :=
  match s.stmt with
  | .expr e => match e.model with | .error s => .error s | .ok e' => .ok (c, [.assign none e'])
  | .assert _ => .error ".assert statement not modeled"
  | .ret e => match e.model with | .error s => .error s | .ok e' => .ok (c, [.ret e'])
  | .declare _ _ => .error ".declare statement not modeled"
  | .letM x _ e =>
      match e.model with
      | .error s => .error s
      | .ok e' =>
      match x with
      | .tuple _ => .error "letM .tuple patterns not modeled"
      | .var n => .ok (c, [.assign (.some n.toString) e'])
  | .setM _ _ _ => .error ".setM statement not modeled"
  | .ifStm _ _ _ => .error ".ifStm statement not modeled"
  | .forLoop x it b => do
    let i' := (KLR.NKI.iterator.model it : Err NML.IteratorS)
    let b' := b.foldlM (fun acc s => KLR.NKI.Stmt.model acc.1 s >>= (fun r => .ok (r.1, acc.2 ++ r.2))) (c, [])
    match i' with
    | .error s => .error s
    | .ok i =>
      match b' with
      | .error s => .error s
      | .ok b =>
        .ok (b.1.it_inc, [
          NML.Stmt.mkiter b.1.fresh_it i,
          NML.Stmt.loop x.toString (.val <| .iref b.1.fresh_it) b.2,
        ])
  | .breakLoop => .error ".breakLoop statement not modeled"
  | .continueLoop => .error ".continueLoop statement not modeled"

-- -- TODO: Inline
-- def KLR.NKI.Stmt.model' (acc : (NKIModelCtx × List (NML.Stmt Float))) (s : NKI.Stmt) :
--    Err (NKIModelCtx × List (NML.Stmt Float)) :=


def NKI.model (k : NKI.Kernel) : Err NMLModel :=
  match k.funs with
  | [f] =>
    match f.body.foldlM (fun acc s => KLR.NKI.Stmt.model acc.1 s >>= (fun r => .ok (r.1, acc.2 ++ r.2))) (.default, []) with
    | .error s => .error s
    | .ok b => .ok { name := f.name, file := f.file, body := b.2}
  | _ => .error "multiple funs not supported"

def NML.Value.pprint : NML.Value Float → String
| .unit => ".unit"
| .bool b => s!".bool {b}"
| .int z => s!".int {z}"
| .data f => s!".data {f}"
| .iref i => s!".iref {i}"
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

def NML.IteratorS.pprint : NML.IteratorS → String
| .affineRange l u s => s!".affineRange {l} {u} {s}"

def NML.Stmt.pprint : NML.Stmt Float → List String
| .ret e => [s!".ret ({e.pprint}),"]
| .assign none e => [s!".assign none ({e.pprint}),"]
| .assign (.some x) e => [s!".assign (some \"{x}\") ({e.pprint}),"]
| .mkiter n i => [s!".mkiter {n} ({i.pprint}),"]
| .loop x it b =>
    let b' := b.map NML.Stmt.pprint |>.flatten  |>.map ("  " ++ ·)
    (s!".loop \"{x}\" {it.pprint} [") :: b' ++ ["]"]
| _ => ["{NML.Stmt.pprint: Not implemented}"]

-- /-- [ frame ] (Internal) Evaluate a list of statements with a given local context. -/
-- | frame        (p : List Stmt) (ctx : LocalContext DataT)
-- /-- [ setp ] Set a single memory location -/
-- | setp         (chip index val : @Expr DataT)


/-- Print out a string representation of the NKI program.
Replaces all floats with a call to the interpretation function. -/
def NKI.pprint (p : NMLModel) : String :=
  let b := p.body.map NML.Stmt.pprint |>.flatten
  let bs :=
    match b with
    | [] => "[]"
    | b1 :: br => (s!"  [ {b1}\n{"\n".intercalate <| br.map ("    " ++ ·)}\n  ]")
s!"-- generated from {p.file}
def {p.name} : NML.ExecState Float :=
  .run
{bs}
  (LocalContext.emp Float)
"

--
