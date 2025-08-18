/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import KLR.Core
import KLR.Py

namespace KLR.NKI.Typed

/-!
# ---------- Typed IR for NKI ---------------
-/

open KLR.Core (Dtype)
open KLR.Py (Span Ident)

inductive Kind
  | unknown
  | size
  | shape
  | typ
deriving BEq

inductive Numeric
  | int
  | float
deriving BEq

inductive Prim
  | none
  | bool
  | numeric (numeric : Numeric)
  | string
  | dtype (dt : Dtype)
deriving BEq

inductive TypBound
  | le (n : Nat)
  | divisibleBy (n : Nat)

structure TypVar where
  name : Ident
  bounds : List TypBound

instance : Coe Ident TypVar where
  coe name := ⟨name, []⟩

inductive Typ
  | var (span : Span) (var : Ident)
  | evar (span : Span) (var : Ident)
  | forall (span : Span) (vars : List TypVar) (body : Typ)
  | prim (span : Span) (p : Prim)
  | func (span : Span) (params : List Typ) (ret : Typ)
  | size (span : Span) (n : Nat)
  | shape (span : Span) (dims : List Typ)
  | tuple (span : Span) (typs : List Typ)
  | list (span : Span) (typ : Typ)
  | tensor (span : Span) (shape : Typ) (dt : Typ)
  | iter (span : Span) (typ : Typ)
  | sizeAdd (span : Span) (x y : Typ)
  | shapeAppend (span : Span) (s1 s2 : Typ)
with
  @[computed_field] isMonotype : Typ → Bool
  | .var _ _             => true
  | .evar _ _            => true
  | .forall _ _ _        => false
  | .prim _ _            => true
  | .func _ params ret   => params.foldl (fun mono typ => mono && typ.isMonotype) ret.isMonotype
  | .size _ _            => true
  | .shape _ dims        => dims.foldl (fun mono typ => mono && typ.isMonotype) true
  | .tuple _ typs        => typs.foldl (fun mono typ => mono && typ.isMonotype) true
  | .list _ typ          => typ.isMonotype
  | .tensor _ sh dt      => sh.isMonotype && dt.isMonotype
  | .iter _ t            => t.isMonotype
  | .sizeAdd _ x y       => x.isMonotype && y.isMonotype
  | .shapeAppend _ s1 s2 => s1.isMonotype && s2.isMonotype

inductive Value
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)

inductive Builtin
  /- unary ops -/
  | neg (t : Numeric) | bitwiseNot | lnot
  /- binary ops -/
  -- logical
  | land | lor
  -- bitwise
  | bitwiseOr | bitwiseXor | bitwiseAnd | lshift | rshift
  -- comparison
  | eq | ne | lt (t : Numeric) | le (t : Numeric) | gt (t : Numeric) | ge (t : Numeric)
  -- arithmetic
  | add (t : Numeric) | sub (t : Numeric)
  | mul (t : Numeric) | div (t : Numeric)
  | mod (t : Numeric) | pow (t : Numeric)
  | floor (t : Numeric)
  /- other -/
  | matmul
  | ite

inductive Exp
  | var (span : Span) (name : Ident)
  | value (span : Span) (value : Value)
  | builtin (span : Span) (value : Builtin)
  | tuple (span : Span) (es : List Exp)
  | list (span : Span) (es : List Exp)
  | call (span : Span) (f : Exp) (typArgs : List Typ) (args : List Exp)

inductive Pattern
  | var (name : Ident)
  | tuple (pats : List Pattern)

inductive Stmt
  | seq (span : Span) (s1 s2 : Stmt)
  | exp (span : Span) (exp : Exp)
  | ret (span : Span) (e : Exp)
  | letBind (span : Span) (name : Ident) (typ : Typ) (rhs : Exp) (body : Stmt)
  | assign (span : Span) (lhs : Exp) (rhs : Exp)
  | assert (span : Span) (e : Exp)
  | funcDef (span : Span) (name : Ident) (typ : Typ) (body : Stmt)
  | ifStm (span : Span) (cond : Exp) (thn : Stmt) (els : Option Stmt)
  | forLoop (span : Span) (pat : Pattern) (iter : Exp) (body : Stmt)
  | whileLoop (span : Span) (cond : Exp) (body : Stmt)
  | pass (span : Span)
  | breakLoop (span : Span)
  | continueLoop (span : Span)

/-! # -------------Utilities on Types------------------- -/

def noneTyp (span : Span) : Typ :=
  .prim span .none

def boolTyp (span : Span) : Typ :=
  .prim span .bool

def intTyp (span : Span) : Typ :=
  .prim span (.numeric .int)

def floatTyp (span : Span) : Typ :=
  .prim span (.numeric .float)

def numericTyp (span : Span) (numeric : Numeric) : Typ :=
  .prim span (.numeric numeric)

def strTyp (span : Span) : Typ :=
  .prim span .string

/--
The free type variables in `t`, including `evar`s
-/
def Typ.ftv (t : Typ) : Std.HashSet Ident :=
  visit {} t
where
  visit (s : Std.HashSet Ident) : Typ → Std.HashSet Ident
  | .var _ v             => s.insert v
  | .evar _ v            => s.insert v
  | .forall _ names body => names.foldl (fun s ⟨n, _⟩ => s.erase n) (visit s body)
  | .prim _ _            => s
  | .func _ params ret   => params.foldl visit (visit s ret)
  | .size _ _            => s
  | .shape _ dims        => dims.foldl visit s
  | .tuple _ typs        => typs.foldl visit s
  | .list _ typ          => visit s typ
  | .tensor _ sh dt      => (visit · sh) <| visit s dt
  | .iter _ typ          => visit s typ
  | .sizeAdd _ x y       => (visit · x) <| visit s y
  | .shapeAppend _ s1 s2 => (visit · s1) <| visit s s2

/-- Check if `a` is a free type variable in `t` -/
def Typ.isFree (t : Typ) (a : Ident) : Bool :=
  t.ftv.contains a

abbrev Substitutions := List (Ident × Typ)

/--
Substitute varialbes bound by `a` in `inTyp` to `toTyp`.

NOTE: If `toTyp` contain a type variable, it must be fresh.
-/
def Typ.subst (inTyp : Typ) (tvar : Ident) (toTyp : Typ) : Typ :=
  match inTyp with
  | .var _ b =>
    if tvar == b then
      toTyp
    else
      inTyp
  | evar _ b =>
    if tvar == b then
      toTyp
    else
      inTyp
  | .forall span names body =>
    if (names.map TypVar.name).contains tvar then
      inTyp
    else
      .forall span names (body.subst tvar toTyp)
  | .prim _ _ => inTyp
  | .func span params ret =>
    let params := params.map (·.subst tvar toTyp)
    let ret := ret.subst tvar toTyp
    .func span params ret
  | .size _ _ => inTyp
  | .shape span dims =>
    let dims := dims.map (·.subst tvar toTyp)
    .shape span dims
  | .tuple span typs =>
    let typs := typs.map (·.subst tvar toTyp)
    .tuple span typs
  | .list span typ =>
    .list span <| typ.subst tvar toTyp
  | .tensor span sh dt =>
    let shape := sh.subst tvar toTyp
    let dt := dt.subst tvar toTyp
    .tensor span shape dt
  | .iter span typ =>
    .iter span <| typ.subst tvar toTyp
  | .sizeAdd span x y =>
    let x := x.subst tvar toTyp
    let y := y.subst tvar toTyp
    .sizeAdd span x y
  | .shapeAppend span s1 s2 =>
    let s1 := s1.subst tvar toTyp
    let s2 := s2.subst tvar toTyp
    .shapeAppend span s1 s2

/--
Apply a lit of substitutions from left to right.
-/
def Typ.applySubsts (inTyp : Typ) (substs : Substitutions) : Typ :=
  substs.foldl (fun inTyp (t, toTyp) => inTyp.subst t toTyp) inTyp

def Exp.subst (e : Exp) (tvar : Ident) (toTyp : Typ) : Exp :=
  match e with
  | .var _ _     => e
  | .value _ _   => e
  | .builtin _ _ => e
  | .tuple span es =>
    .tuple span (es.map (·.subst tvar toTyp))
  | .list span es =>
    .list span (es.map (·.subst tvar toTyp))
  | .call span f typArgs args =>
    .call span
      (f.subst tvar toTyp)
      (typArgs.map (·.subst tvar toTyp))
      (args.map (·.subst tvar toTyp))

/--
Apply a lit of substitutions from left to right.
-/
def Exp.applySubsts (inExp : Exp) (substs : Substitutions) : Exp :=
  substs.foldl (fun inExp (t, toTyp) => inExp.subst t toTyp) inExp

mutual

def Stmt?.subst (s : Option Stmt) (tvar : Ident) (toTyp : Typ) : Option Stmt :=
  match s with
  | some s => some (s.subst tvar toTyp)
  | none => none

def Stmt.subst (s : Stmt) (tvar : Ident) (toTyp : Typ) : Stmt :=
  match s with
  | .seq span s1 s2 =>
    .seq span (s1.subst tvar toTyp) (s2.subst tvar toTyp)
  | .exp span e =>
    .exp span (e.subst tvar toTyp)
  | .ret span e =>
    .ret span (e.subst tvar toTyp)
  | .letBind span name typ rhs body =>
    let typ := typ.subst tvar toTyp
    let rhs := rhs.subst tvar toTyp
    let body := body.subst tvar toTyp
    .letBind span name typ rhs body
  | .assign span lhs rhs =>
    let lhs := lhs.subst tvar toTyp
    let rhs := rhs.subst tvar toTyp
    .assign span lhs rhs
  | .assert span e =>
    .assert span (e.subst tvar toTyp)
  | .funcDef span name typ body =>
    if !typ.isFree tvar then s else
    let typ := typ.subst tvar toTyp
    let body := body.subst tvar toTyp
    .funcDef span name typ body
  | .ifStm span cond thn els =>
    let cond := cond.subst tvar toTyp
    let thn := thn.subst tvar toTyp
    let els := Stmt?.subst els tvar toTyp
    .ifStm span cond thn els
  | .forLoop span pat iter body =>
    let iter := iter.subst tvar toTyp
    let body := body.subst tvar toTyp
    .forLoop span pat iter body
  | .whileLoop span cond body =>
    let cond := cond.subst tvar toTyp
    let body := body.subst tvar toTyp
    .whileLoop span cond body
  | .pass _ => s
  | .breakLoop _ => s
  | .continueLoop _ => s

end

/--
Apply a lit of substitutions from left to right.
-/
def Stmt.applySubsts (inStmt : Stmt) (substs : Substitutions) : Stmt :=
  substs.foldl (fun inStmt (a, toTyp) => inStmt.subst a toTyp) inStmt

/-! # ---------Getting the types of various language constructs------- -/

def Value.typ (span : Span) : Value → Typ
  | .none     => .prim span .none
  | .bool   _ => .prim span .bool
  | .int    _ => .prim span (.numeric .int)
  | .float  _ => .prim span (.numeric .float)
  | .string _ => .prim span .string

def Builtin.typ (span : Span) : Builtin → Typ
  | .neg n =>
    let t := numericTyp span n
    .func span [t] t
  | .bitwiseNot =>
    let t := intTyp span
    .func span [t] t
  | .lnot =>
    let t := boolTyp span
    .func span [t] t
  | .land | .lor =>
    let t := boolTyp span
    .func span [t, t] t
  | .bitwiseOr | .bitwiseXor | .bitwiseAnd | .lshift | .rshift =>
    let t := intTyp span
    .func span [t, t] t
  | .eq | .ne =>
    let vt := Typ.var span "A"
    let bt := boolTyp span
    .forall span ["A"] <| .func span [vt, vt] bt
  | .lt n | .le n | .gt n | .ge n =>
    let nt := numericTyp span n
    let bt := boolTyp span
    .func span [nt, nt] bt
  | .add n | .sub n
  | .mul n | .div n
  | .mod n | .pow n
  | .floor n =>
    let t := numericTyp span n
    .func span [t, t] t
  | .matmul =>
    let DT := Typ.var span "DT"
    let M := Typ.var span "M"
    let K := Typ.var span "K"
    let N := Typ.var span "N"
    .forall span ["DT", "M", "K", "N"] <|
      .func span
        [.tensor span (.shape span [M, N]) DT,
        .tensor span (.shape span [K, N]) DT]
        (.tensor span (.shape span [M, N]) DT)
  | .ite =>
    let bt := boolTyp span
    let vt := Typ.var span "A"
    .forall span ["A"] <| .func span [bt, vt, vt] vt

/-! # ---------Utilities------- -/

def Typ.span : Typ → Span
  | .var span _
  | .evar span _
  | .forall span _ _
  | .prim span _
  | .func span _ _
  | .size span _
  | .shape span _
  | .tuple span _
  | .list span _
  | .tensor span _ _
  | .iter span _
  | .sizeAdd span _ _
  | .shapeAppend span _ _
    => span

def Numeric.max : Numeric → Numeric → Numeric
  | .float, _
  | _, .float => .float
  | .int, .int => .int

/--
This is used to properly type if-statements.
If either side of the if-statement is `None`, then the whole thing should be `None`.
If the two sides return different types, then the whole thing will also be `None`.
But we also need to upgrade `int`s to `float`s whenever necessary.
-/
def Typ.min : Typ → Typ → Typ
  | .prim span .none, _
  | _, .prim span .none => .prim span .none
  | .prim span (.numeric n1), .prim _ (.numeric n2) =>
    .prim span (.numeric (n1.max n2))
  | .prim span p1, .prim _ p2 =>
    if p1 == p2 then
      .prim span p1
    else
      .prim span .none
  | .var span α, .var _ β => if α == β then .var span α else .prim span .none
  | .evar span α, .evar _ β => if α == β then .evar span α else .prim span .none
  /- TODO: handle other cases -/
  | t, _ => .prim t.span .none

def Exp.span : Exp → Span
  | .var span _
  | .value span _
  | .builtin span _
  | .tuple span _
  | .list span _
  | .call span _ _ _
    => span

def Stmt.span : Stmt → Span
  | .seq span _ _
  | .exp span _
  | .ret span _
  | .letBind span _ _ _ _
  | .assign span _ _
  | .assert span _
  | .funcDef span _ _ _
  | .ifStm span _ _ _
  | .forLoop span _ _ _
  | .whileLoop span _ _
  | .pass span
  | .breakLoop span
  | .continueLoop span
    => span

/-! # ---------Pretty print types------- -/

def Kind.toString : Kind → String
  | .unknown => "unknown"
  | .size => "size"
  | .shape => "shape"
  | .typ => "type"

def Numeric.toString : Numeric → String
  | .int => "int"
  | .float => "float"

def Prim.toString : Prim → String
  | .none => "None"
  | .bool => "bool"
  | .numeric n => n.toString
  | .string => "str"
  | .dtype dt => dt.toString

def Typ.toString : Typ → String
  | .var _ name          => name
  | evar _ name          => s!"?{name}"
  | .forall _ vars body =>
    let names := vars.map TypVar.name
    let whereBounds := (vars.map fun {name, bounds} => bounds.map fun bound => (name, bound)).flatten
    let whereBounds :=
      if whereBounds.isEmpty then "" else
      let bounds := whereBounds.map fun (name, bound) =>
        match bound with
        | .le n => s!"{name} <= {n}"
        | .divisibleBy n => s!"{n} | {name}"
      s!" where {", ".intercalate bounds}"
    s!"forall {" ".intercalate names}. {body.toString}{whereBounds}"
  | .prim _ p            => p.toString
  | .func _ params ret   => s!"[{", ".intercalate (params.map Typ.toString)}] -> {ret.toString}"
  | .size _ n            => s!"{n}"
  | .shape _ dims        => s!"({", ".intercalate (dims.map Typ.toString)})"
  | .tuple _ typs        => s!"tuple[{", ".intercalate (typs.map Typ.toString)}]"
  | .list _ typ          => s!"list[{typ.toString}]"
  | .tensor _ sh dt      => s!"tensor[{sh.toString}, {dt.toString}]"
  | .iter _ typ          => s!"iter[{typ.toString}]"
  | .sizeAdd _ x y       => s!"{x.toString} + {y.toString}"
  | .shapeAppend _ s1 s2 => s!"{s1.toString} @ {s2.toString}"

instance : ToString Kind := ⟨Kind.toString⟩
instance : ToString Numeric := ⟨Numeric.toString⟩
instance : ToString Prim := ⟨Prim.toString⟩
instance : ToString Typ := ⟨Typ.toString⟩
