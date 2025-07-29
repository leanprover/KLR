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

import KLR.NKI.Typed.Common

namespace KLR.NKI.Typed.PIR
open Lean (ToJson)

/-!
# Python IR

High-level IR for NKI that closely resembles the python concrete syntax
-/

abbrev Ident := Lean.Name

mutual

structure Typ where
  pos : Pos := {}
  typ : Typ'
deriving ToJson

inductive Typ'
  | var (name : Ident)
  | prim (p : Prim)
  | arrow (α β : Typ)
  | all (argName : Ident) (body : Typ)
  | iter (e : Typ)
  | tuple (ts : List Typ)
  | list (t : Typ)
deriving Repr, ToJson

end

inductive Value
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | tensor (value : TensorLib.Tensor)
deriving ToJson

inductive UnaryOp
  | neg
deriving ToJson

inductive BinOp
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub
  | mul | div
  | mod | pow
  | floor
deriving BEq, ToJson

mutual

structure Arg where
  keyword : Option Ident
  val : Exp
deriving ToJson

inductive Index
  | coord (i : Exp)
  | slice (l u step : Option Exp)
  | ellipsis

structure Exp where
  pos : Pos := {}
  exp : Exp'
deriving ToJson

inductive Exp'
  | var (name : Ident)
  | value (value : Value)
  | unaryOp (op : UnaryOp) (x : Exp)
  | binOp (op : BinOp) (x y : Exp)
  | tuple (es : List Exp)
  | list (es : List Exp)
  | ifExp (test body orelse : Exp)
  | app (f : Exp) (typArgs : List Typ) (args : List Arg)
  | access (e : Exp) (indices : List Index)
deriving ToJson

end

inductive Pattern
  | var (name : Ident)
  | tuple (pats : List Pattern)
deriving ToJson

structure Param where
  name : Ident
  typ : Option Typ
  dflt : Option Exp
deriving ToJson

mutual

structure Def where
  pos : Pos
  name : Ident
  typParams : List Ident
  params : List Param
  returns : Option Typ
  body : Stmt
  decorator : Option Ident
deriving ToJson

structure Stmt where
  pos : Pos := {}
  stmt : Stmt'
deriving ToJson

inductive Stmt'
  | seq (e1 e2 : Stmt)
  | exp (exp : Exp)
  | ret (e : Exp)
  | assign (pat : Pattern) (typ : Option Typ) (rhs : Exp)
  | dfn (dfn : Def)
  | ifStm (cond : Exp) (thn : Stmt) (elifs : List (Exp × Stmt)) (els : Option Stmt)
  | forLoop (name : Ident) (iter : Exp) (body : Stmt)
  | whileLoop (cond : Exp) (body : Stmt)
  | breakLoop
  | continueLoop
deriving ToJson

end

open Std (Format)
open Std.Format (joinSep)

def maxPrec := 1000

structure Prog where
  file : String
  defs : List Def
deriving ToJson

def TabWidth := 2

def br : Format := "\n"

def paren (f : Format) : Format :=
  "(" ++ f ++ ")"

def braket (f : Format) : Format :=
  "[" ++ f ++ "]"

mutual

def Typ.listReprPrec : List Typ → Nat → List Format
  | [], _ => []
  | hd :: tl, p => hd.reprPrec p :: Typ.listReprPrec tl p

def Typ.collectArrowRhs : Typ → Nat → List Format
  | { typ, .. }, p => typ.collectArrowRhs p

def Typ'.collectArrowRhs : Typ' → Nat → List Format
  | .arrow α β, p =>
    let α := α.reprPrec p
    let βs := β.collectArrowRhs p
    α :: βs
  | t, p => [t.reprPrec p]

def Typ.collectAllRhs : Typ → Nat → (List Format) × Format
  | { typ, .. }, p => typ.collectAllRhs p

def Typ'.collectAllRhs : Typ' → Nat → (List Format) × Format
  | .all argName body, p =>
    let arg := s!"{argName}"
    let (args, body) := body.collectAllRhs p
    (arg :: args, body)
  | t, p => ([], t.reprPrec p)

def Typ.reprPrec : Typ → Nat → Format
  | { typ, .. }, p => typ.reprPrec p

def Typ'.reprPrec : Typ' → Nat → Format
  | .var name, _ => s!"{name}"
  | .prim p, _ => s!"{p}"
  | .arrow α β, _ =>
    let α := α.reprPrec 0
    let βs := β.collectArrowRhs 0
    let ts := joinSep (α :: βs) ", "
    s!"FuntionType[{ts}]"
  | .all argName body, _ =>
    let arg : Format := s!"{argName}"
    let (args, body) := body.collectAllRhs 0
    let args := joinSep (arg :: args) " "
    s!"forall {args}. {body}"
  | .iter e, _ => s!"Iterable[{e.reprPrec 0}]"
  | .tuple ts, _ =>
    let ts := joinSep (Typ.listReprPrec ts 0) ", "
    s!"tuple[{ts}]"
  | .list t, _ =>
    s!"list[{t.reprPrec 0}]"

end

instance instReprTyp : Repr Typ where
  reprPrec t n := Typ.reprPrec t n

def Value.reprPrec : Value → Nat → Format
  | .none, _ => "None"
  | .bool value, _ => match value with | true => "True" | false => "False"
  | .int value, _ => s!"{value}"
  | .float value, _ => s!"{value}"
  | .string value, _ => s!"\"{value.escape '"'}\""
  | .tensor _, _ => s!"nl.ndarray(sorry)"

instance instReprValue : Repr Value where
  reprPrec v n := Value.reprPrec v n

/--
See https://docs.python.org/3/reference/expressions.html#operator-precedence
-/
def UnaryOp.reprPrec : UnaryOp → String × Nat
  | .neg => ("-", 95)

/--
Associativity of operators.
- `l` means left-associative
- `r` means right-associative
- `c` means the operator is commutative
-/
inductive Assoc | l | r | c

/--
See https://docs.python.org/3/reference/expressions.html#operator-precedence
-/
def BinOp.reprPrec : BinOp → String × Nat × Assoc
  | .pow => ("**", 100, .r)
  | .mul => ("*", 90, .c) | .div => ("/", 90, .l) | .floor => ("//", 90, .l) | .mod => ("%", 90, .l)
  | .add => ("+", 85, .c) | .sub => ("-", 85, .l)
  | .ge => (">=", 80, .r) | .gt => (">", 80, .r) | .le => ("<=", 80, .r) | .lt => ("<", 80, .r) | .ne => ("!=", 80, .r) | .eq => ("==", 80, .r)
  | .land => ("and", 75, .c)
  | .lor => ("or", 70, .c)

mutual

def Exp.optionReprPrec : Option Exp → Nat → Option Format
  | some e, p => some <| e.reprPrec p
  | none, _ => none

def Index.reprPrec : Index → Nat → Format
  | .coord i, p => i.reprPrec p
  | .slice l u step, _ =>
    let l := Exp.optionReprPrec l 0 |> Option.getD Format.nil
    let u := Exp.optionReprPrec u 0 |> Option.getD Format.nil
    let step := Exp.optionReprPrec step 0
    match step with
    | some step => s!"{l}:{u}:{step}"
    | none => s!"{l}:{u}"
  | .ellipsis, _ => "..."

def Arg.reprPrec : Arg → Nat → Format
  | ⟨none, val⟩, p => val.reprPrec p
  | ⟨some kw, val⟩, p => s!"{kw}={val.reprPrec p}"

def Exp.reprPrec : Exp → Nat → Format
  | { exp, .. }, p => exp.reprPrec p

def Exp'.reprPrec : Exp' → Nat → Format
  | .var name, _ => s!"{name}"
  | .value value, _ => value.reprPrec 0
  | .unaryOp op x, p =>
    let (op, opP) := op.reprPrec
    let x := x.reprPrec opP
    let fmt := s!"{op}{x}"
    if opP < p then paren fmt else fmt
  | .binOp op x y, p =>
    let (opStr, opP, assoc) := op.reprPrec
    let (opL, opR) :=
      match assoc with
      | .l => (opP, opP + 1)
      | .r => (opP + 1, opP)
      | .c => (opP, opP)
    let x := x.reprPrec opL
    let y := y.reprPrec opR
    let fmt := if op == .pow then s!"{x}{opStr}{y}" else s!"{x} {opStr} {y}"
    if opP < p then paren fmt else fmt
  | .tuple es, _ =>
    let es := es.map (fun e => e.reprPrec 0)
    let len := es.length
    let es := joinSep es ", "
    let es := if len == 1 then es ++ "," else es
    paren es
  | .list es, _ =>
    let es := es.map (fun e => e.reprPrec 0)
    let len := es.length
    let es := joinSep es ", "
    let es := if len == 1 then es ++ "," else es
    braket es
  | .ifExp test body orelse, p =>
    let opP := 65
    let test := test.reprPrec 0
    let body := body.reprPrec 0
    let orelse := orelse.reprPrec 0
    let fmt := s!"{body} if {test} else {orelse}"
    if opP < p then paren fmt else fmt
  | .app f typArgs args, _ =>
    let f := f.reprPrec maxPrec
    let typArgs := typArgs.map (fun t => t.reprPrec 0)
    let typArgs := joinSep typArgs ", "
    let args := args.map (·.reprPrec 0)
    let args := joinSep args ", "
    if typArgs.isEmpty then
      s!"{f}({args})"
    else
      s!"{f}[{typArgs}]({args})"
  | .access e indices, _ =>
    let e := e.reprPrec maxPrec
    let indices := indices.map (·.reprPrec 0)
    let indices := joinSep indices ", "
    s!"{e}[{indices}]"

end

instance instReprExp : Repr Exp where
  reprPrec e n := e.reprPrec n

def Stmt.reprPrec (s : Stmt) (prec : Nat) : Format :=
  sorry

def Def.reprPrec (d : Def) (prec : Nat) : Format :=
  sorry

def Prog.reprPrec (p : Prog) (prec : Nat) : Format :=
  sorry
