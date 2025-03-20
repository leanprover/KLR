/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import ISA.Basic

/-
# A (not so) pretty printer for Lean

Note, this is incomplete. We need to sort everything into dependency order,
and figure out how to organize the output into Lean files.
-/

namespace ISA.Generate
open Std (Format)

def unop : UnOp -> Format := repr
def binop : BinOp -> Format
  | .plus          => " + "
  | .minus         => " - "
  | .multiply      => " * "
  | .divide        => " / "
  | .modulo        => " % "
  | .shiftLeft     => " << "
  | .shiftRight    => " >> "
  | .bitwiseInvert => " ~ "
  | .bitwiseOr     => " | "
  | .bitwiseAnd    => " & "
  | .bitwiseXor    => " ^ "
  | .logicalOr     => " || "
  | .logicalAnd    => " && "

def cmpop : CmpOp -> Format
  | .eq => " == "
  | .ne => " != "
  | .ge => " >= "
  | .gt => " > "
  | .le => " <= "
  | .lt => " < "

def typ : Typ -> Format
  | .bool => "Bool"
  | .u8 => "UInt8"
  | .u16 => "UInt16"
  | .u32 => "UInt32"
  | .usize => "UInt64"
  | .i8 => "Int8"
  | .i16 => "Int16"
  | .i32 => "Int32"
  | .inst => "Inst"
  | .named s => .text s
  | .vec t n => "Vec " ++ typ t ++ repr n

def typedef (name : String) (t : Typ) : Format :=
  .text ("abbrev " ++ name ++ " := ") ++ typ t

def flattenOp (op : BinOp) (e : Expr) : List Expr :=
  match e with
  | .binop op2 l r =>
    if op == op2
    then flattenOp op l ++ flattenOp op r
    else [l, r]
  | _ => [e]

def flattenBinOp (op : BinOp) (l r : Expr) : List Expr :=
  if op.commutes
  then flattenOp op l ++ flattenOp op r
  else [l, r]

partial def expr (e : Expr) (useParen : Bool := false) : Format :=
  let paren := if useParen then Format.paren else id
  let expr e := expr e true
  match e with
  | .int i => repr i
  | .var v => v.toString
  | .cast e b false => paren (expr e ++ " as u" ++ repr b)
  | .cast e b true => paren (expr e ++ " as i" ++ repr b)
  | .proj l r => .joinSep [expr l, expr r] "."
  | .index l r => expr l ++ .sbracket (expr r)
  | .unop op e => unop op ++ expr e
  | .binop op l r =>
      let es := flattenBinOp op l r
      .group (paren $ .joinSep (es.map expr) (binop op ++ .line))
  | .cmp op l r => paren (.joinSep [expr l, expr r] (cmpop op))
  | .cond c t e => paren $ .joinSep [expr c, "?", expr t, ":", expr e] " "
  | .call f args => f.toString ++ .paren (.joinSep (args.map expr) ", ")

def const (name : String) (value : Expr) : Format :=
  .join [.text name, .text " = ", expr value]

def enum (name : String) (variants : List (String × Expr)) : Format :=
  let vs := variants.map fun (n,_) => .indentD ("| " ++ n)
  let header := .text ("inductive " ++ name ++ " where")
  .join (header :: vs)

def struct (name : String) (entries : List (String × Typ)) (isInst : Bool := false): Format :=
  let es := entries.map fun (n,t) => .indentD (n ++ " : " ++ typ t)
  let header :=
    if isInst
    then .text ("structure " ++ name ++ " extends Inst where")
    else .text ("structure " ++ name ++ " where")
  .join (header :: es)

def union (name : String) (entries : List (String × Typ)) : Format :=
  .nil

def function (f : Function) : Format :=
  let args := f.args.map fun (n,t) => Format.indentD $ Format.paren (n ++ " : " ++ typ t)
  let header := Format.line ++ "def " ++ f.name ++ .group (.joinSep args " ")
  header ++ " : " ++ typ f.ret ++ " :=" ++ .indentD (expr f.expr)

def assert (_name : String) (funs : List Function) : Format :=
  let fs := funs.map fun f => function f
  .joinSep fs .line

def item : ISAItem -> Format
  | .enum name vs => enum name vs
  | .struct name es => struct name es
  | .union name es => union name es

def inst (i : InstFormat) : Format :=
  let fmt := struct i.name i.fields (isInst := true) ++ .line
  let insts := i.opcodes.map fun op =>
    .text s!"structure {op} extends {i.name} where" ++
    .indentD (s!"opcode = .{op}" ++ .line)
  let funs := i.checks.toList.map fun (_,f) => function f
  Format.joinSep (fmt :: insts ++ funs) .line

def print : Format -> IO Unit
  | .nil => pure ()
  | fmt => IO.println (fmt.pretty (width := 80))

def generate (isa : ISA) : IO Unit := do
  for (n, t) in isa.types do
    print (typedef n t)

  for (_, i) in isa.insts do
    print (inst i)
