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

private def args [ToFormat a] (l : List a) : Format :=
  .paren (.joinSep l ",")

private def sqArgs [ToFormat a] (l : List a) : Format :=
  .sbracket (.joinSep l ",")

instance [ToFormat a] [ToFormat b] : ToFormat (a × b) where
  format | (a,b) => .paren (format a ++ "," ++ format b)

instance : ToFormat Memory where
  format
  | .hbm => "hbm"
  | .sbuf => "sbuf"
  | .pmem => "pmem"
  | .reg  => "reg"

instance : ToFormat Dtype where
  format dty :=
    match (reprStr dty).toName with
    | .str _ name => name
    | _ => impossible "dtype repr must be a name"

instance : ToFormat Address where
  format a := format a.memory ++ sqArgs [format a.partitionOffset, format a.freeOffset, format a.size]

instance : ToFormat Shape where
  format s := sqArgs (s.parDim :: s.freeDims)

instance : ToFormat TensorName where
  format t := t.name

instance : ToFormat Slice where
  format s := .joinSep [format s.l, format s.u, format s.step] ":"

instance : ToFormat Index where
  format
  | .coord i => format i
  | .slice s => format s

instance : ToFormat AccessBasic where
  format acc := format acc.tensor ++ sqArgs acc.indexes

instance : ToFormat APPair where
  format ap := args [ap.step, Int.ofNat ap.num]

instance : ToFormat AccessPattern where
  format ap := format ap.tensor ++ (.sbracket <| sqArgs <|
    format ap.offset :: format ap.parNum :: ap.freePattern.map format)

instance : ToFormat Access where
  format
  | .simple t => format t
  | .basic acc => format acc
  | .pattern ap => format ap

instance : ToFormat Operator where
  format
  | .load => "load"
  | .save => "save"
  | .const => "const"
  | .tensorScalar .. => "tensor_scalar{..}"
  | .tensorScalarAddr .. => "tensor_scalar_addr{..}"

instance : ToFormat Value where
  format
  | .var x    => x
  | .bool b   => format b
  | .int i    => format i
  | .float f  => format f
  | .access a => format a

instance : ToFormat Expr where
  format
  | .value v => format v
  | .call f a k => format f ++ args (a ++ k.map Prod.snd)

instance : ToFormat Stmt where
  format
  | .ret e => "ret" ++ format e
  | .assign x e => x ++ " = " ++ format e
  | .store d op as => format d ++ " := " ++ format op ++ args as

def ppFullTensor (t : TensorName) : Format :=
  t.name ++ sqArgs [ format t.dtype, format t.shape, format t.address ]

instance : ToFormat Kernel where
  format k :=
    let lines l := Format.joinSep l .line
    let nest_lines l := Format.nest 2 (.align true ++ lines l)
    lines [
      Format.text k.name,
      "inputs:", nest_lines (k.inputs.map ppFullTensor),
      "outputs:", nest_lines (k.outputs.map ppFullTensor),
      "internal:", nest_lines (k.internal.map ppFullTensor),
      "body:", nest_lines (k.body.map format)
    ]
