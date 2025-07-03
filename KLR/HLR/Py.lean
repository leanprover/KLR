/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.HLR.AST
import KLR.Util
import SHerLOC
import TensorLib.Shape
import TensorLib.Slice

open Std.Format
open TensorLib (Dtype Shape Slice)

/-
This module converts an HLR program into a runnable Python program.
At present, it can't convert HLR constants to python constants and can't
take input tensors, so it is only helpful to ensure that the shape
annotations are correct and that the program is well-formed.
-/
namespace KLR.HLR.Py

structure FormatCtx where
  indent : Nat := 0
  program : String := ""

abbrev Format := Std.Format

def dTypeToPy : Dtype → String
  | .bool => "np.bool_"
  | .int8 => "np.int8"
  | .int16 => "np.int16"
  | .int32 => "np.int32"
  | .int64 => "np.int64"
  | .uint8 => "np.uint8"
  | .uint16 => "np.uint16"
  | .uint32 => "np.uint32"
  | .uint64 => "np.uint64"
  | .float32 => "np.float32"
  | .float64 => "np.float64"

def binOpToPy : BinaryOp → String
  | .add => "np.add"
  | .sub => "np.subtract"
  | .mul => "np.multiply"
  | .div => "np.divide"
  | .and => "np.logical_and"
  | .max => "np.maximum"
  | .cmp => "np.compare"

def unaryOpToPy : UnaryOp → String
  | .exp => "np.exp"
  | .sqrt => "np.sqrt"
  | .neg => "np.negative"
  | .convert d => s!"(lambda x: x.as_type({dTypeToPy d}))"

def reduceOpToPy : BinaryOp → String
  | .add => "np.sum"
  | .max => "np.max"
  | op => panic! s!"Unsupported reduction operation: {op}"

def intLitToPy : StableHLO.Parsing.IntegerLiteral → String
  | .mk .plus decimal => s!"{decimal}"
  | .mk .minus decimal => s!"-{decimal}"

def floatLitToPy : StableHLO.Parsing.FloatLiteral → String
  | .decimal (.mk intPart fracPart sciPart) =>
    let intPartStr := intLitToPy intPart
    let fracPartStr := intLitToPy fracPart
    let sciPartStr := intLitToPy sciPart
    s!"{intPartStr}.{fracPartStr}e{sciPartStr}"
  | .hexaDecimal n => toString n

def elementLitToPy : StableHLO.Parsing.ElementLiteral → String
  | .booleanLiteral .true => "True"
  | .booleanLiteral .false => "False"
  | .floatLiteral f => floatLitToPy f
  | .complexLiteral { real, imaginary } =>
    s!"complex({floatLitToPy real}, {floatLitToPy imaginary})"
  | .stringLiteral str => s!"'{str}'"

def valueToPy : StableHLO.Parsing.DenseLiteral → String
  | .denseDimension n => s!"[{n.map valueToPy |> ", ".intercalate}]"
  | .denseElements arr => ",".intercalate (arr.map elementLitToPy)

def shapeToPy (s : Shape) : String :=
  s.val.map toString |> ",".intercalate

def varToPy (arg : Var) : String :=
  -- Prefix, since Python variables can't start with a digit
  s!"var_{arg}"

def opToPy (op : Operator) : String :=
  match op with
  | .arg index => s!"args[{index}]"
  | .binaryOp binOp a b => s!"{binOpToPy binOp}({varToPy a}, {varToPy b})"
  | .unaryOp unOp a => s!"{unaryOpToPy unOp}({varToPy a})"
  | .reductionOp redOp a b dim => s!"{reduceOpToPy redOp}({varToPy a}, initial={varToPy b}, axis={dim[0]!})"
  | .batchMatmul a b => s!"np.einsum(\"bij,bkj->bik\", {varToPy a}, {varToPy b})"
  | .arange start stop step shape => s!"np.arange({start}, {stop}, {step}).reshape({shapeToPy shape})"
  | .concat tensors dim =>
    let tensorsStr := String.intercalate "," (tensors.map toString)
    s!"np.concatenate([{tensorsStr}], axis={dim})"
  | .select cond a b => s!"np.where({cond}, {varToPy a}, {varToPy b})"
  | .full value shape => s!"np.full(({shapeToPy shape}), {value})"
  | .transpose a dims =>
    let dimsStr := dims.map toString |> ", ".intercalate
    s!"np.transpose({varToPy a}, axes=[{dimsStr}])"
  | .split_with_sizes .. => panic! s!"Split with sizes operation not implemented in Python translation"
  | .reshape a shape => s!"{varToPy a}.reshape({shapeToPy shape})"
  | .broadcast a shape dims => s!"jax.lax.broadcast_in_dim({varToPy a}, ({shapeToPy shape}), {dims})"
  | .const _ shape _ => s!"np.random.random(({shapeToPy shape})" -- TODO: make this use the actual constant value
  | .gather .. => panic! s!"Gather operation not implemented in Python translation"
  | .slice .. => panic! s!"Slice operation not implemented in Python translation"
  | .call .. =>
    panic! s!"Can't translate call operators to Python"

def compileStatement (s : Statement) : Format :=
  match s with
  | .comment msg => text s!"# {msg}"
  | .assign dest op {shape, ..} =>
    text (s!"{varToPy dest} = {opToPy op} # {shape}") ++
    if shape.ndim != 0 then
      line ++ text (s!"assert {varToPy dest}.shape == ({shapeToPy shape},), \"Expected %s, got %s\" % (({shapeToPy shape}), {varToPy dest}.shape)")
    else
      nil
  | .ret vars =>
    let varNames := vars.map varToPy |> ", ".intercalate
    text s!"return {varNames}"

def compileFunction (f : Function) : Format :=
    let inputsStr := f.inputs.map (fun {shape, ..} => s!"\"np.ndarray[({shapeToPy shape})]\"") |> ", ".intercalate |> fun x => s!"args: Tuple[{x}]"
    let outputsStr := f.outputs.map (fun {shape, ..} => shapeToPy shape) |> ", ".intercalate
    let funcHeader := s!"def {f.name}({inputsStr}) -> (\"np.ndarray[({outputsStr})]\"):"
    let args := f.inputs.map (fun {shape, ..} => s!"np.random.random(({shapeToPy shape}))")
    let funCall := s!"{f.name}([{", ".intercalate args}])"
    text funcHeader ++
    (nest 4 (prefixJoin line (f.statements.map compileStatement))) ++ line ++
    text funCall

def compileProgram (p : Program) : Format :=
    let lines := [
      text "import numpy as np",
      text "import jax",
      text "from typing import Tuple"] ++
      p.functions.map compileFunction
    joinSep lines line

-- Compile the HLR program to a Python program.
def compile (p : Program) : String :=
  (compileProgram p).pretty

end KLR.HLR.Py
