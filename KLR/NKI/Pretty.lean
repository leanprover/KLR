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

import KLR.NKI.Basic

namespace KLR.NKI
open Std

private def abracket (f : Format) : Format :=
  .bracket "<" f ">"

private def sbracket (f : Format) : Format :=
  .bracket "[" f "]"

private def braces (f : Format) : Format :=
  .bracket "{" f "}"

private def spaces [ToFormat a] (l : List a) : Format :=
  .joinSep l " "

private def args [ToFormat a] (l : List a) : Format :=
  .paren (.joinSep l ",")

private def sqArgs [ToFormat a] (l : List a) : Format :=
  .sbracket (.joinSep l ",")

instance : ToFormat Value where
  format
  | .none => "None"
  | .bool true => "True"
  | .bool false => "False"
  | .int i => format i
  | .float f => format f
  | .string s => .bracket "\"" s "\""
  | .tensor shape dty name =>
    abracket (format shape ++ "," ++ dty ++ "," ++ format name)

instance : ToFormat BinOp where
  format op :=
    match (reprStr op).toName with
    | .str _ name => name
    | n => n.toString  -- impossible?

mutual
private def expr (e : Expr) (nested : Bool := false) : Format :=
  expr' e.expr nested
  termination_by sizeOf e
  decreasing_by cases e; simp; omega

private def expr' (e : Expr') (nested : Bool := false) : Format :=
  let parens f := if nested then Format.paren f else f
  match e with
  | .value v => format v
  | .var n => n.toString
  | .tuple es => parens (.joinSep (es.map expr) ",")
  | .list es => sbracket (.joinSep (es.map expr) ",")
  | .dict es => braces (args (es.map keyword))
  | .access e i => expr e ++ sqArgs (i.map index)
  | .binOp op l r => parens $ spaces [expr l, format op, expr r]
  | .conj l r => parens (expr l true ++ " and " ++ expr r true)
  | .disj l r => parens (expr l true ++ " or " ++ expr r true)
  | .ifExp c t f => parens (expr t ++ " if " ++ expr c ++ " else " ++ expr f)
  | .call f xs kws => expr f ++ args (xs.map (expr (nested := true)) ++ kws.map keyword)
  | .object c fs => c ++ args (fs.map keyword)
  termination_by sizeOf e

private def exprOpt (oe : Option Expr) : Format :=
  match oe with
  | none => "None"
  | some e => expr e true
  termination_by sizeOf oe

private def index (i : Index) : Format :=
  match i with
  | .coord i => expr i true
  | .slice l u s => .joinSep [exprOpt l, exprOpt u, exprOpt s] ":"
  | .ellipsis => "..."
  termination_by sizeOf i

private def keyword (kw : Keyword) : Format :=
  .joinSep [.text kw.name, expr kw.expr (nested := true)] "="
  termination_by sizeOf kw
  decreasing_by cases kw; simp; omega
end

instance : ToFormat Expr := ⟨ expr ⟩
instance : ToFormat Expr' := ⟨ expr' ⟩
instance : ToFormat Index := ⟨ index ⟩
instance : ToFormat Keyword := ⟨ keyword ⟩

private def pattern (p : Pattern) : Format :=
  match p with
  | .var n =>  n.toString
  | .tuple ps => args (ps.map pattern)

instance : ToFormat Pattern := ⟨ pattern ⟩

instance : ToFormat RangeType where
  format rt := toString rt

instance : ToFormat Iterator where
  format
  | .expr e => expr e
  | .range ty l u s => format ty ++ "_range" ++ args [expr l, expr u, expr s]

mutual
private def stmt (s : Stmt) : Format :=
  stmt' s.stmt
  termination_by sizeOf s
  decreasing_by cases s; simp; omega

private def stmts (l : List Stmt) : Format :=
  .nest 2 (.align true ++ .joinSep (l.map stmt) .line)
  termination_by sizeOf l

private def stmt' (s : Stmt') : Format :=
  match s with
  | .expr e => expr e
  | .assert e => "assert " ++ expr e
  | .ret e => "ret " ++ expr e
  | .declare x ty => x.toString ++ " : " ++ expr ty
  | .letM p none e => format p ++ " = " ++ expr e
  | .letM p (some t) e => format p ++ " : " ++ expr t ++ " = " ++ expr e
  | .setM x e false => expr x ++ " = " ++ expr e
  | .setM x e true => expr x ++ " += " ++ expr e
  | .ifStm cond thn els =>
      "if " ++ expr cond ++ ":" ++ .line ++
        stmts thn ++
      "else:" ++ .line ++
        stmts els
  | .forLoop x iter body =>
      "for " ++ x.toString ++ " in " ++ format iter ++ ":" ++ .line ++
        stmts body
  | .breakLoop => "break"
  | .continueLoop => "continue"
  termination_by sizeOf s
end

instance : ToFormat Stmt := ⟨ stmt ⟩
instance : ToFormat Stmt' := ⟨ stmt' ⟩

instance : ToFormat Param where
  format
  | ⟨ name, none ⟩ => name
  | ⟨ name, some e ⟩ => name ++ " = " ++ expr e

instance : ToFormat Fun where
  format f :=
    f.name ++ args (f.args.map format) ++ ":" ++ .line ++
      stmts f.body

instance : ToFormat Arg where
  format | ⟨ name, e ⟩ => name ++ " = " ++ expr e

instance : ToFormat Kernel where
  format k :=
    .joinSep (k.globals.map format) .line ++ .line ++
    .joinSep (k.funs.map format) .line ++ .line ++
    k.entry ++ args (k.args.map format)
