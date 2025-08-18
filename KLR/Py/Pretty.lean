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

import KLR.Py.Basic

/-!
# A pretty printer for the Python AST

Currently, this can only be used for debugging.
To make this suitable for fuzzing the production compiler
or as a code formatter, at least the following needs to be fixed:

- Properly handle escape sequences when printing string literal
- Distinguish between long strings ("""s""") and short string ("s")
- Handle comments and white spaces (for code formatting)
-/

def String.escape (s : String) (char : Char → Bool) : String :=
  ⟨go s.toList⟩
where
  go
  | [] => []
  | '\\' :: c :: tl => '\\' :: c :: go tl
  | c :: tl =>
    if char c then
      '\\' :: c :: go tl
    else
      c :: go tl

namespace KLR.Py

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

def Prim.toString : Prim → String
  | .bool => "bool"
  | .none => "None"
  | .string => "str"
  | .numeric .int => "int"
  | .numeric .float => "float"
  | .dtype dt => dt.toString

mutual

def Typ'.reprPrec : Typ' → Nat → Format
  | .var id, _ => id
  | .prim p, _ => p.toString
  | .list t, _ => s!"list[{t.reprPrec 0}]"
  | .iter t, _ => s!"iter[{t.reprPrec 0}]"
  | .tuple ts, _ =>
    let ts := ts.map (·.reprPrec 0)
    s!"tuple[{joinSep ts ", "}]"
  | .tensor sh dt, _ =>
    let sh := sh.reprPrec 0
    let dt := dt.reprPrec 0
    s!"tensor[{sh}, {dt}]"
  | .size n, _ => s!"{n}"
  | .shape dims, _ =>
    let dims := dims.map (·.reprPrec 0)
    s!"({joinSep dims ", "})"
  | .func params ret, _ =>
    let params := params.map (·.reprPrec 0)
    let ret := ret.reprPrec 0
    s!"[{joinSep params ", "}] -> {ret}"
  | .forall names body, _ =>
    let body := body.reprPrec 0
    s!"forall {joinSep names " "}. {body}"
  | .sizeAdd x y, _ =>
    let x := x.reprPrec 0
    let y := y.reprPrec 0
    s!"{x} + {y}"
  | .shapeAppend s1 s2, _ =>
    let s1 := s1.reprPrec 0
    let s2 := s2.reprPrec 0
    s!"{s1} @ {s2}"

def Typ.reprPrec : Typ → Nat → Format
  | { typ, .. }, n => typ.reprPrec n

end

def Value.reprPrec : Value → Nat → Format
  | .none, _ => "None"
  | .bool value, _ => match value with | true => "True" | false => "False"
  | .int value, _ => s!"{value}"
  | .float value, _ => s!"{value}"
  | .string value, _ =>
    -- TODO: this does not escape everything, e.g. newlines, tabs, ascii bell, etc.
    s!"\"{value.escape (fun c => c == '"' || c == '\'')}\""
  | .ellipsis, _ => "..."

instance instReprValue : Repr Value where
  reprPrec v n := Value.reprPrec v n

/--
See https://docs.python.org/3/reference/expressions.html#operator-precedence
-/
def UnaryOp.reprPrec : UnaryOp → String × Nat
  | .neg => ("-", 100)
  | .pos => ("+", 100)
  | .bitwiseNot => ("~", 100)
  | .lnot => ("not", 55)

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
  | .pow => ("**", 95, .r)
  | .mul => ("*", 90, .c) | .matmul => ("@", 90, .c) | .div => ("/", 90, .l) | .floor => ("//", 90, .l) | .mod => ("%", 90, .l)
  | .add => ("+", 85, .c) | .sub => ("-", 85, .l)
  | .lshift => ("<<", 80, .l) | .rshift => (">>", 80, .l)
  | .bitwiseAnd => ("&", 75, .l)
  | .bitwiseXor => ("^", 70, .l)
  | .bitwiseOr => ("|", 65, .l)
  | .ge => (">=", 60, .c) | .gt => (">", 60, .c) | .le => ("<=", 60, .c) | .lt => ("<", 60, .c) | .ne => ("!=", 60, .c) | .eq => ("==", 60, .c)
  | .land => ("and", 50, .c)
  | .lor => ("or", 45, .c)

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
    let fmt := if op == "not" then s!"{op} {x}" else s!"{op}{x}"
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
    let es := joinSep es ", "
    braket es
  | .ifExp test body orelse, p =>
    -- TODO: check precedence here
    let opP := 40
    let test := test.reprPrec 41
    let body := body.reprPrec 41
    let orelse := orelse.reprPrec 40
    let fmt := s!"{body} if {test} else {orelse}"
    if opP < p then paren fmt else fmt
  | .call f typArgs args, p =>
    -- TODO: check precedence here
    let opP := 110
    let f := f.reprPrec 110
    let typArgs := typArgs.map (fun t => t.reprPrec 0)
    let typArgs := joinSep typArgs ", "
    let args := args.map (·.reprPrec 0)
    let args := joinSep args ", "
    let fmt :=
      if typArgs.isEmpty then
        s!"{f}({args})"
      else
        s!"{f}[{typArgs}]({args})"
    if opP < p then paren fmt else fmt
  | .access e indices, p =>
    let opP := 105
    let e := e.reprPrec 105
    let indices := indices.map (·.reprPrec 0)
    let indices := joinSep indices ", "
    let fmt := s!"{e}[{indices}]"
    if opP < p then paren fmt else fmt
  | .attr e field, p =>
    let opP := 110
    let e := e.reprPrec 110
    let fmt := s!"{e}.{field}"
    if opP < p then paren fmt else fmt

end

instance instReprExp' : Repr Exp' where
  reprPrec e n := e.reprPrec n

instance instToStringExp' : ToString Exp' where
  toString e := s!"{e.reprPrec 0}"

instance instReprExp : Repr Exp where
  reprPrec e n := e.reprPrec n

instance instToStringExp : ToString Exp where
  toString e := s!"{e.reprPrec 0}"

instance instToStringIndex : ToString Index where
  toString i := s!"{i.reprPrec 0}"

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

def Exp.reprPrecNoOuterParen (e : Exp) (prec : Nat) : Format :=
  match e.exp with
  | .tuple es =>
    let es := es.map (Exp.reprPrec · prec)
    let len := es.length
    let es := joinSep es ", "
    if len == 1 then es ++ "," else es
  | _ => e.reprPrec prec

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
  | { name, typParams, params, returns, body, decorators, whereBounds }, _ =>
    let typParams :=
      if typParams.isEmpty then
        Format.nil
      else
        braket <| joinSep typParams ", "
    let params := paren <| group <| align false ++ joinSep (params.map (·.reprPrec 0)) ", "
    let returns := (returns.map ((" -> " : Format) ++ ·.reprPrec 0)).getD Format.nil
    let whereBounds : Format :=
      if whereBounds.isEmpty then "" else
      let es := whereBounds.map (Exp.reprPrec · 0)
      br ++ "where" ++ nest (br ++ (joinSep es br)) ++ br
    let body := Stmt.listReprPrec body 0
    let decorators :=
      if decorators.isEmpty then
        Format.nil
      else
        (joinSep (decorators.map (("@" : Format) ++ ·.reprPrec 0)) br) ++ br
    decorators ++ s!"def {name}{typParams}{params}" ++ returns ++ whereBounds ++ ":" ++ nest (br ++ body)

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
  | .assign lhs typ rhs, _ =>
    let lhs := lhs.reprPrecNoOuterParen 0
    let typ := (typ.map ((" : " : Format) ++ ·.reprPrec 0)).getD Format.nil
    let rhs := rhs.reprPrecNoOuterParen 0
    s!"{lhs}{typ} = {rhs}"
  | .assert e, _ =>
    let e := e.reprPrec 0
    s!"assert {e}"
  | .funcDef dfn, _ => dfn.reprPrec 0
  | .ifStm cond thn elifs els, _ =>
    let cond := cond.reprPrec 0
    let thn := Stmt.listReprPrec thn 0
    let if_ := s!"if {cond}:" ++ nest (br ++ thn)

    let elifs := Stmt.listExpStmtsReprPrec elifs 0
    let elifs := elifs.map (fun (cond, body) => s!"elif {cond}:" ++ nest (br ++ body))
    let elifs := if elifs.isEmpty then Format.nil else br ++ joinSep elifs br

    let els := Stmt.optionListReprPrec els 0
    let els := els.map (fun els => br ++ s!"else:" ++ nest (br ++ els))
    let els := els.getD Format.nil

    if_ ++ elifs ++ els
  | .forLoop pat iter body, _ =>
    let pat := pat.reprPrec 0
    let iter := iter.reprPrec 0
    let body := Stmt.listReprPrec body 0
    s!"for {pat} in {iter}:" ++ nest (br ++ body)
  | .whileLoop cond body, _ =>
    let cond := cond.reprPrec 0
    let body := Stmt.listReprPrec body 0
    s!"while {cond}:" ++ nest (br ++ body)
  | .pass, _ => "pass"
  | .breakLoop, _ => "break"
  | .continueLoop, _ => "continue"

end

instance instReprStmt : Repr Stmt where
  reprPrec := Stmt.reprPrec

instance instToStringStmt : ToString Stmt where
  toString s := s!"{Stmt.reprPrec s 0}"

def Prog.reprPrec (p : Prog) (_ : Nat) : Format :=
  let stmts := p.stmts.map (·.reprPrec 0)
  joinSep stmts (br ++ br)

instance instReprProg : Repr Prog where
  reprPrec := Prog.reprPrec

instance instToStringProg : ToString Prog where
  toString p := s!"{Prog.reprPrec p 0}"

def Prog.prettyPrint (p : Prog) : String :=
  (p.reprPrec 0).pretty
