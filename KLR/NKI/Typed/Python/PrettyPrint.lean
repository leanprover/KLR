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

import KLR.NKI.Typed.Python.Basic

def String.escape (s : String) (char : Char) : String :=
  ⟨go s.toList⟩
where
  go
  | [] => []
  | '\\' :: c :: tl => '\\' :: c :: go tl
  | c :: tl =>
    if c == char then
      '\\' :: c :: go tl
    else
      c :: go tl


namespace KLR.NKI.Typed.Python

open Std (Format)
open Std.Format (group align joinSep)

def ppMaxPrec := 1000

def tabWidth := 2

def nest (f : Format) :=
  Std.Format.nest tabWidth f

def br : Format := "\n"

def paren (f : Format) : Format :=
  "(" ++ f ++ ")"

def braket (f : Format) : Format :=
  "[" ++ f ++ "]"

mutual

def Typ.listReprPrec : List Typ → Nat → List Format
  | [], _ => []
  | hd :: tl, p => hd.reprPrec p :: Typ.listReprPrec tl p

def Typ.reprPrec : Typ → Nat → Format
  | { typ, .. }, p => typ.reprPrec p

def Typ'.reprPrec : Typ' → Nat → Format
  | .var name, _ => name
  | .prim p, _ => s!"{p}"
  | .func typParams params, _ =>
    let params := joinSep (params.map (Typ.reprPrec · 0)) ", "
    let body := s!"FunctionType[{params}]"
    if typParams.length > 0 then
      s!"forall {joinSep typParams " "}. {body}"
    else
      body
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

NOTE: Chaining of comparisons are disallowed by the parser. See `KLR.NKI.Typed.Python.Parser.Parse.pExp`
-/
def BinOp.reprPrec : BinOp → String × Nat × Assoc
  | .pow => ("**", 100, .r)
  | .mul => ("*", 90, .c) | .div => ("/", 90, .l) | .floor => ("//", 90, .l) | .mod => ("%", 90, .l)
  | .add => ("+", 85, .c) | .sub => ("-", 85, .l)
  | .ge => (">=", 80, .c) | .gt => (">", 80, .c) | .le => ("<=", 80, .c) | .lt => ("<", 80, .c) | .ne => ("!=", 80, .c) | .eq => ("==", 80, .c)
  | .land => ("and", 75, .c)
  | .lor => ("or", 70, .c)

mutual

def Exp.optionReprPrec : Option Exp → Nat → Option Format
  | some e, p => some <| e.reprPrec p
  | none, _ => none

def Index.reprPrec : Index → Nat → Format
  | .coord i, p => i.reprPrec p
  | .slice l u step, _ =>
    let l : Format := (Exp.optionReprPrec l 0).getD Format.nil
    let u : Format := (Exp.optionReprPrec u 0).getD Format.nil
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
  | .var name, _ => name
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
    -- TODO: check precedence here
    let opP := 65
    let test := test.reprPrec 67
    let body := body.reprPrec 65
    let orelse := orelse.reprPrec 66
    let fmt := s!"{body} if {test} else {orelse}"
    if opP < p then paren fmt else fmt
  | .call f typArgs args, _ =>
    -- TODO: check precedence here
    let f := f.reprPrec ppMaxPrec
    let typArgs := typArgs.map (fun t => t.reprPrec 0)
    let typArgs := joinSep typArgs ", "
    let args := args.map (·.reprPrec 0)
    let args := joinSep args ", "
    if typArgs.isEmpty then
      s!"{f}({args})"
    else
      s!"{f}[{typArgs}]({args})"
  | .access e indices, _ =>
    let e := e.reprPrec ppMaxPrec
    let indices := indices.map (·.reprPrec 0)
    let indices := joinSep indices ", "
    s!"{e}[{indices}]"
  | .attr e field, _ =>
    let e := e.reprPrec ppMaxPrec
    s!"{e}.{field}"

end

instance instReprExp : Repr Exp where
  reprPrec e n := e.reprPrec n

def Pattern.reprPrec : Pattern → Nat → Format
  | .var name, _ => name
  | .tuple names, p =>
    let names := names.map (·.reprPrec 1)
    let len := names.length
    let pat := joinSep names ", "
    let pat := if len == 1 then pat ++ "," else pat
    if p > 0 then paren pat else pat

instance instReprPattern : Repr Pattern where
  reprPrec := Pattern.reprPrec

def Param.reprPrec (p : Param) (prec : Nat) : Format :=
  let typ := (p.typ.map ((":" : Format) ++ ·.reprPrec prec)).getD Format.nil
  let dflt := (p.dflt.map (("=" : Format) ++ ·.reprPrec prec)).getD Format.nil
  p.name ++ typ ++ dflt

mutual

def Stmt.optionListReprPrec : Option (List Stmt) → Nat → Option Format
  | some stmts, p => some <| Stmt.listReprPrec stmts p
  | none, _ => none

def Stmt.listExpStmtsReprPrec : List (Exp × List Stmt) → Nat → List (Format × Format)
  | [], _ => []
  | (e, s) :: tl, p => (e.reprPrec p, Stmt.listReprPrec s p) :: Stmt.listExpStmtsReprPrec tl p

def Stmt.reprPrec : Stmt → Nat → Format
  | { stmt, .. }, p => stmt.reprPrec p

def FuncDef.reprPrec : FuncDef → Nat → Format
  | { name, typParams, params, returns, body, decorators, .. }, _ =>
    let typParams :=
      if typParams.isEmpty then
        Format.nil
      else
        braket <| joinSep typParams ", "
    let params := paren <| group <| align false ++ joinSep (params.map (·.reprPrec 0)) ", "
    let returns := (returns.map ((" -> " : Format) ++ ·.reprPrec 0)).getD Format.nil
    let body := Stmt.listReprPrec body 0
    let decorators :=
      if decorators.isEmpty then
        Format.nil
      else
        (joinSep (decorators.map (("@" : Format) ++ ·.reprPrec 0)) br) ++ br
    decorators ++ s!"def {name}{typParams}{params}" ++ returns ++ ":" ++ br ++ nest body

def Stmt.listReprPrec (stmts : List Stmt) (prec : Nat) : Format :=
  let stmts := stmts.map (·.reprPrec prec)
  joinSep stmts br

def Stmt'.reprPrec : Stmt' → Nat → Format
  | .exp exp, _ => exp.reprPrec 0
  | .imprt mod as, _ =>
    let imp := s!"import {mod}"
    match as with
    | some as => s!"{imp} as {as}"
    | none => imp
  | .imprtFrom mod imp as, _ =>
    let imp := s!"from {mod} import {imp}"
    match as with
    | some as => s!"{imp} as {as}"
    | none => imp
  | .ret e, _ =>
    let e := e.reprPrec 0
    s!"return {e}"
  | .assign pat typ rhs, _ =>
    let pat := pat.reprPrec 0
    let typ := (typ.map ((" : " : Format) ++ ·.reprPrec 0)).getD Format.nil
    let rhs :=
      match rhs.exp with
      | .tuple es =>
        let es := es.map (Exp.reprPrec · 0)
        let len := es.length
        let es := joinSep es ", "
        if len == 1 then es ++ "," else es
      | _ => rhs.reprPrec 0
    s!"{pat}{typ} = {rhs}"
  | .assert e, _ =>
    let e := e.reprPrec 0
    s!"assert {e}"
  | .funcDef dfn, _ => dfn.reprPrec 0
  | .ifStm cond thn elifs els, _ =>
    let cond := cond.reprPrec 0
    let thn := Stmt.listReprPrec thn 0
    let if_ := s!"if {cond}:" ++ br ++ nest thn

    let elifs := Stmt.listExpStmtsReprPrec elifs 0
    let elifs := elifs.map (fun (cond, body) => s!"elif {cond}:" ++ br ++ nest body)
    let elifs := joinSep elifs br

    let els := Stmt.optionListReprPrec els 0
    let els := els.map (fun els => s!"else:" ++ br ++ nest els)
    let els := els.getD Format.nil

    if_ ++ elifs ++ els
  | .forLoop name iter body, _ =>
    let iter := iter.reprPrec 0
    let body := Stmt.listReprPrec body 0
    s!"for {name} in {iter}:" ++ br ++ nest body
  | .whileLoop cond body, _ =>
    let cond := cond.reprPrec 0
    let body := Stmt.listReprPrec body 0
    s!"while {cond}:" ++ br ++ nest body
  | .pass, _ => "pass"
  | .breakLoop, _ => "break"
  | .continueLoop, _ => "continue"

end

instance instReprStmt : Repr Stmt where
  reprPrec := Stmt.reprPrec

def Prog.reprPrec (p : Prog) (_ : Nat) : Format :=
  let stmts := p.stmts.map (·.reprPrec 0)
  joinSep stmts (br ++ br)

instance instReprProg : Repr Prog where
  reprPrec := Prog.reprPrec

def Prog.prettyPrint (p : Prog) : String :=
  (p.reprPrec 0).pretty
