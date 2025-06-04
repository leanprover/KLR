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
  | .string s => .ok <| .string s
  | .tensor _ _ _ => .error "tensor values not added" -- TODO: I think this is a ptr

def List.hasKW (L : List NKI.Keyword) (n : String) : Err NKI.Expr :=
  match L with
  | .nil => .error s!"missing kwarg {n}"
  | k :: ks => if k.name == n then .ok k.expr else ks.hasKW n

-- FIXME: this is just a hack to write regular monadic code since the Err monad
-- is giving me tons of universe problems
def Err.Bind' (e : Err α) (f : α → Err β) : Err β :=
  match e with | .error s => .error s | .ok v => f v


partial def KLR.NKI.Expr.model (s : NKI.Expr) : Err (NML.Expr Float) :=
  match s.expr with
  | .value v => match v.model with | .error s => .error s | .ok e' => .ok <| .val e'
  | .var n => .ok <| .var n.toString
  | .tuple e =>
      Err.Bind' (e.foldlM (fun acc e => Err.Bind' (model e) (.ok <| acc ++ [·])) []) <| fun le =>
      .ok (.tup le)
  | .list .. => .error "list no modeled"
  | .access _ _ => .error "access not modeled"
  | .binOp _ _ _ => .error "binop not modeled"
  | .conj _ _ => .error "conj not modeled"
  | .disj _ _ => .error "disj not modeled"
  | .ifExp _ _ _ => .error "ifExp not modeled"
  | .call f args kws =>
      match f.expr with
      -- Semantics for nisa.memset
      | .var (.str (.str .anonymous "nisa") "memset") =>
        Err.Bind' (kws.hasKW "dst") <| fun dst =>
        Err.Bind' (KLR.NKI.Expr.model dst) <| fun edst =>
        Err.Bind' (kws.hasKW "name") <| fun name =>
        Err.Bind' (KLR.NKI.Expr.model name) <| fun _ =>
        Err.Bind' (kws.hasKW "value") <| fun value =>
        Err.Bind' (KLR.NKI.Expr.model value) <| fun evalue =>
        Err.Bind' (kws.hasKW "dtype") <| fun dtype =>
        Err.Bind' (KLR.NKI.Expr.model dtype) <| fun _ =>
        -- TODO: Ignoring the name and dtype fields at the moment
        -- TODO: NKI is parsing dtypes as variables for some reason
        match evalue with
        | .val (.data v) => .ok <| .dunop edst (.cst v)
        | _ => .error "bad value in nisa memset"
      | .var (.str (.str .anonymous "sbuf") "view") =>
        match args with
        | [_, shape, dst] =>
          Err.Bind' (KLR.NKI.Expr.model shape) <| fun eshape =>
          Err.Bind' (KLR.NKI.Expr.model dst) <| fun edst =>
          .ok <| .view eshape edst
        | _ => .error "bad sbuf view call"
      | .var (.str (.str .anonymous "nisa") "tensor_scalar") =>
        Err.Bind' (kws.hasKW "data") <| fun v =>
        Err.Bind' (kws.hasKW "op0") <| fun op0 =>
        Err.Bind' (kws.hasKW "operand0") <| fun oper0 =>
        Err.Bind' (KLR.NKI.Expr.model v) <| fun data =>
        match op0, oper0 with
        | ⟨.var x, _⟩, ⟨.var s, _⟩ =>
          if x.toString = "np.add"
            then  .error s!"TODO: emit an .tsdunop statement here."
            else  .error s!"unsupported operand {x}"
        | _, _ => .error s!"bad operands to tensor_scalar:\n{Lean.toJson op0}\n \n {Lean.toJson oper0}"
      | _ => .error s!"call not modeled {Lean.toJson f}"

-- TODO: Add Iterator expression steps to the model.
-- Right now, all iterator expressions must be static.
def KLR.NKI.iterator.model : Iterator → Err NML.IteratorS
  | .expr _ => .error ".expr iterators no modeled"
  | .range _ l u s =>
      Err.Bind' (KLR.NKI.Expr.model l) <| fun (zl : NML.Expr Float) =>
      Err.Bind' (KLR.NKI.Expr.model u) <| fun zu =>
      Err.Bind' (KLR.NKI.Expr.model s) <| fun zs =>
      match zl, zu, zs with
      | .val (.int zl), .val (.int zu), .val (.int zs) =>
        if (0 < zs) then .ok <| IteratorS.affineRange zl zu (zs - 1).toNat else .error "negative or zero number of steps"
      | _, _, _ => .error "bad call to iterator"
-- TODO: Cleanup
partial def KLR.NKI.Stmt.model (c : NKIModelCtx) (s : NKI.Stmt) : Err (NKIModelCtx × List (NML.Stmt Float)) :=
  match s.stmt with
  -- TODO: This right now is special-cased because it is modeled as two statements
  | .letM (.var x) _ ⟨.call ⟨.var (.str (.str .anonymous "nl") "zeros"), _⟩ args _, _⟩ =>
      match args with
      | [_, _, _] => .ok ⟨c, [
          .assign (some x.toString) (.alloc .sbuf),
          .tsdunop (.var "ℓ") .cst (.val <| .int 0) -- TODO: This should be float
        ]⟩
      | _ => .error s!"Special case in nl.zeroes not modeled"
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
| .string s => s!".string \"{s}\""
| .data f => s!".data (NMLEnv.intoDataT {f})"
| .iref i => s!".iref {i}"
| .tupV l => s!".tupV [{", ".intercalate (l.map pprint)}]"
| _ => "sorry /- NML.Value.pprint: Not implemented -/"

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

def NML.Dunop.pprint : NML.Dunop Float → String
| .cst f => s!".cst (NMLEnv.intoDataT {f})"
| .lean _ => "«Lean function»"

def NML.Expr.pprint : NML.Expr Float → String
| .val v => s!".val ({v.pprint})"
| .var x => s!".var \"{x}\""
| .tup l => s!".tup [{", ".intercalate (l.map pprint)}]"
| .dunop d f => s!".dunop ({d.pprint}) ({f.pprint})"
| .view e1 e2 => s!".view ({e1.pprint}) ({e2.pprint})"
| _ => "sorry /- NML.Expr.pprint: Not implemented -/"

def NML.IteratorS.pprint : NML.IteratorS → String
| .affineRange l u s => s!".affineRange {l} {u} {s}"

def NML.Stmt.pprint : NML.Stmt Float → List String
| .ret e => [s!".ret ({e.pprint}),"]
| .assign none e => [s!".assign none ({e.pprint}),"]
| .assign (.some x) e => [s!".assign (.some \"{x}\") ({e.pprint}),"]
| .mkiter n i => [s!".mkiter {n} ({i.pprint}),"]
| .loop x it b =>
    let b' := b.map NML.Stmt.pprint |>.flatten  |>.map ("  " ++ ·)
    (s!".loop \"{x}\" ({it.pprint}) [") :: b' ++ ["],"]
| _ => ["sorry /- NML.Stmt.pprint: Not implemented -/"]



def NKI.pprint_body (p : NMLModel) : String :=
  let b := p.body.map NML.Stmt.pprint |>.flatten
  match b with
  | [] => "[]"
  | b1 :: br => (s!"  [ {b1}\n{"\n".intercalate <| br.map ("    " ++ ·)}\n  ]")

/-- Print out the NML model of a program -/
def NKI.pprint_standalone_model (p : NMLModel) : String :=
s!"import KLR.Semantics

namespace model
open NML

/- The type of floating point numbers.

You should restrict this generic type using typeclasses, or instantiate
it with the type of floats you care about. The proof framework will still
work without specializing DataT whatsoever. -/
variable \{DataT : Type _} [NMLEnv DataT]

/-- NML model of {p.name}. Generated from file {p.file}. -/
def {p.name} : NML.ProgState DataT :=
  ⟨.run ⟨
{NKI.pprint_body p}, .emp⟩, []⟩

end model"

-- TODO: Erasure and ret_assert

/-- Print out the NML model of a program -/
def NKI.pprint_relational_goal (pl pr : NMLModel) : String :=
s!"import KLR.Semantics

namespace model
open Iris.BI.BIBase KLR.Core Iris NML Iris.BI

/- The type of floating point numbers.

You should restrict this generic type using typeclasses, or instantiate
it with the type of floats you care about. The proof framework will still
work without specializing DataT whatsoever. -/
variable \{DataT : Type _} [NMLEnv DataT]

/-- Stuttering bound. This can be set to any value. -/
abbrev K : Nat := sorry

/-- (Pure) relational postcondion. -/
def Φ : NML.Value DataT → NML.Value DataT → Prop := sorry

/-- State precondition.
You are free to assume any valid fragmental ownership to begin with.
See the adequacy theorem.
-/
def σI : @PROP DataT := emp -- TODO: Generate these automatically

/-- NML model of {pl.name}. Generated from file {pl.file}. -/
def sL : NML.ProgState DataT :=
  ⟨.run ⟨
{NKI.pprint_body pl}, .emp⟩, []⟩

/-- NML model of {pr.name}. Generated from file {pr.file}. -/
def sR : NML.ProgState DataT :=
  ⟨.run ⟨
{NKI.pprint_body pr}, .emp⟩, []⟩

theorem sLsR_equiv : σI ⊢ wp (DataT := DataT) K sL sR (ΦPure Φ) := by
  -- Equivalence proof
  sorry

-- From here, sLsR_equiv can be used in conjunction with the adequacy theorem
-- to conclude that sL and sR are related by PRelS, or if sL = sR = s the
-- safety theorem will allow you to conclude that s is safe.

end model"



/-
namespace example7
/-! Example: Loop exit -/

abbrev K : LeibnizO Nat := ⟨2⟩
variable (n : Nat) (i : Iterator DataT) (b : List (Stmt DataT))
variable (Hloop : PLoopExit (LocalContext.bindi .emp n i) n)

@[simp] def sL : ExecState DataT := .run [
    .loop "x" (.val <| .iref n) b,
    .ret <| (.val .unit)
  ] (LocalContext.bindi .emp n i)
@[simp] def sR : ExecState DataT := .run [
    .ret <| (.val .unit)
  ] .emp

example : ⊢ wp (DataT := DataT) K (sL n i b) sR (ΦPure ΦTriv) := by
  istart
  wp_desync
  uwp_left  SPure.uwpL .loopExit Hloop
  uwp_left  SPure.uwpL .ret trivial
  uwp_right SPure.uwpR .ret trivial
  wp_resync
  wp_sync_val
  unfold ΦPure ΦTriv
  ipure_intro
  grind

end example7
-/
