/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core.Basic
import KLR.Util

namespace KLR.Core
open Std

/-
This is a simple pretty printer for KLR terms. At some point, we may want to
make this output valid python syntax that would parse and elaborate to the same
KLR kernel. At the moment, there are too many unknowns to spend time on this.
The format here is just for ease of debugging, feel free to modify as you wish.
-/

private def abracket (f : Format) : Format :=
  Format.bracket "<" f ">"

private def ppArgs [ToFormat a] (l : List a) : Format :=
  Format.joinSep l ","

def ppMemory : Memory -> Format
  | .dram => "dram"
  | .sbuf => "sbuf"
  | .pmem => "pmem"
  | .reg => "reg"

def ppTensor (t : TensorName) : Format := t.name

def ppConst : Const -> Format
  | .none       => "None"
  | .bool true  => "True"
  | .bool false => "False"
  | .int i      => format i
  | .float f    => format f
  | .string s   => "\"" ++ s.push '"'

private def addParens : Nat -> Format -> Format
  | 0, f => f
  | _, f => f.paren

def ppIndexExpr (n : Nat) : IndexExpr -> Format
  | .var x      => x
  | .int i      => format i
  | .neg e      => "-" ++ ppIndexExpr (n+1) e
  | .add l r    => addParens n $ ppIndexExpr 1 l ++ "+" ++ ppIndexExpr 1 r
  | .mul i e    => addParens n $ format i ++ "*" ++ ppIndexExpr 1 e
  | .floor e i  => addParens n $ ppIndexExpr 1 e ++ "/" ++ format i
  | .ceil e i   => "ceil" ++ Format.paren (ppIndexExpr 0 e ++","++ format i)
  | .mod e i    => addParens n $ ppIndexExpr 1 e ++ "%" ++ format i

def ppIndexExpr? : Option IndexExpr -> Format
  | none   => "None"
  | some e => ppIndexExpr 0 e

def ppIndex : Index -> Format
  | .ellipsis    => "..."
  | .coord e     => ppIndexExpr? e
  | .slice none none none => ":"
  | .slice none u none => "0:" ++ ppIndexExpr? u
  | .slice s u none => .joinSep ([s,u].map ppIndexExpr?) ":"
  | .slice l u s => .joinSep ([l,u,s].map ppIndexExpr?) ":"

def ppOperator : Operator -> Format
  | .tensorScalar _ => "tensor_scalar{..}"

private def ppList (f : a -> Format) : List a -> Format
  | [] => .nil
  | x :: xs => .append (f x) (ppList f xs)

partial def ppExpr : Expr -> Format
  | .var x => x
  | .const c => ppConst c
  | .tensor t => ppTensor t
  | .access t [.ellipsis] => ppExpr t
  | .access t ix => .fill (ppExpr t ++ .sbracket (.joinSep (ix.map ppIndex) ","))
  | .operator op => ppOperator op
  | .call f args kwargs =>
      let args := args.map ppExpr
      let kwargs := kwargs.map fun (x,e) => x ++ "=" ++ ppExpr e
      .fill (ppExpr f ++ .paren (ppArgs (args ++ kwargs)))

def ppStmt : Stmt -> Format
  | .ret e      => "ret" ++ ppExpr e
  | .store t ix e => ppExpr (.access (.tensor t) ix) ++ " := " ++ ppExpr e
  | .assign x e => x ++ " = " ++ ppExpr e
  | .loop _ _ _ _ _ => "<loop>"

def ppDtype (dty : Dtype) : Format :=
  match (reprStr dty).toName with
  | .str _ name => name
  | _ => impossible "dtype repr must be a name"

def ppFullTensor (t : TensorName) : Format :=
  t.name ++ abracket (.joinSep [
    ppDtype t.dtype,
    .paren (.joinSep t.shape ","),
    ppMemory t.memory
    ] ",")

def lines (l : List Format) := Format.joinSep l "\n"
def nest_lines (l : List Format) := Format.nest 2 (.align true ++ lines l)

def ppKernel (k : Kernel) : Format :=
  lines [
    Format.text k.name,
    "inputs:", nest_lines (k.inputs.map ppFullTensor),
    "outputs:", nest_lines (k.outputs.map ppFullTensor),
    "internal:", nest_lines (k.internal.map ppFullTensor),
    "body:", nest_lines (k.body.map ppStmt)
  ]

instance : ToFormat Dtype      where format := ppDtype
instance : ToFormat TensorName where format := ppTensor
instance : ToFormat Const      where format := ppConst
instance : ToFormat IndexExpr  where format := ppIndexExpr 0
instance : ToFormat Index      where format := ppIndex
instance : ToFormat Operator   where format := ppOperator
instance : ToFormat Expr       where format := ppExpr
instance : ToFormat Stmt       where format := ppStmt
instance : ToFormat Kernel     where format := ppKernel
