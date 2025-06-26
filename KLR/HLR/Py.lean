/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.HLR.AST
import KLR.Core.Operators
import KLR.Util
import SHerLOC
import TensorLib.Shape
import TensorLib.Slice

namespace KLR.HLR

structure FormatCtx where
  indent : Nat := 0
  program : String := ""

abbrev Format := EStateM String FormatCtx

def increaseIndent : Format Unit := do
  modify (fun ctx => { ctx with indent := ctx.indent + 4 })
def decreaseIndent : Format Unit := do
  modify (fun ctx => { ctx with indent := max 0 (ctx.indent - 4) })
def getIndent : Format String := do
  let ctx ← get
  pure (List.replicate ctx.indent " " |> String.join)

def putLn (msg : String) : Format Unit := do
  let ctx ← get
  let indentStr ← getIndent
  let newLine := s!"{indentStr}{msg}\n"
  pure (← set { ctx with program := ctx.program ++ newLine })

class ToPy (T : Type) where
  toPy : T → Format Unit

def binOpToPy (op : BinaryOp) : String :=
  match op with
  | .mul => "multiply"
  | .max => "maximum"
  | .sub => "subtrace"
  | .add => "add"
  | .div => "divide"
  | .cmp => "compare"
  | .and => "logical_and"
def unaryOpToPy (op : UnaryOp) : String :=
  match op with
  | .exp => "exp"
  | .sqrt => "sqrt"
  | .neg => "negative"
  | .convert => "convert"
def reduceOpToPy (op : BinaryOp) : String :=
  match op with
  | .max => "max"
  | .add => "sum"
  | _ => s!"assert false # Unsupported reduction operation {repr op}"

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
def elementLitToPy (v : StableHLO.Parsing.ElementLiteral) : String :=
  match v with
  | .booleanLiteral .true => "True"
  | .booleanLiteral .false => "False"
  | .floatLiteral f => floatLitToPy f
  | .complexLiteral { real, imaginary } =>
    s!"complex({floatLitToPy real}, {floatLitToPy imaginary})"
  | .stringLiteral str => s!"'{str}'"
def valueToPy (v : StableHLO.Parsing.DenseLiteral) : String :=
  match v with
  | .denseDimension n => s!"[{n.map valueToPy |> ", ".intercalate}]"
  | .denseElements arr => ",".intercalate (arr.map (fun x => elementLitToPy x))

def shapeToPy (s : Shape) : String :=
  s.val.map toString |> ",".intercalate

def varToPy (arg : Var) : String :=
  s!"var_{arg}" -- Prefix to avoid python naming issues

def opToPy (op : Operator) : String :=
  match op with
  | .arg index => s!"np.array(args[{index}], dtype=np.int32)"
  | .binaryOp binOp a b => s!"np.{binOpToPy binOp}({varToPy a}, {varToPy b})"
  | .unaryOp unOp a => s!"np.{unaryOpToPy unOp}({varToPy a})"
  | .reductionOp redOp a b dim => s!"np.{reduceOpToPy redOp}({varToPy a}, initial={varToPy b}, axis={dim[0]!})"
  | .batchMatmul a b _ => s!"np.einsum(\"bij,bkj->bik\", {varToPy a}, {varToPy b})"
  | .arange start stop step shape => s!"np.arange({start}, {stop}, {step}).reshape({shapeToPy shape})"
  | .concat tensors dim =>
    let tensorsStr := String.intercalate "," (tensors.map (fun t => s!"{t}"))
    s!"np.concatenate([{tensorsStr}], axis={dim})"
  | .select cond a b => s!"np.where({cond}, {varToPy a}, {varToPy b})"
  | .full value shape => s!"np.full(({shapeToPy shape}), {floatLitToPy value}, dtype=np.float32)"
  | .transpose a dims =>
    let dimsStr := dims.map toString |> ", ".intercalate
    s!"np.transpose({varToPy a}, axes=[{dimsStr}])"
  | .split_with_sizes _ _ => panic! s!"Split with sizes operation not implemented in Python translation"
  | .reshape a shape => s!"{varToPy a}.reshape({shapeToPy shape})"
  | .broadcast a shape => s!"np.broadcast_to({varToPy a}, shape=({shapeToPy shape}))"
  | .const _ shape => s!"np.full(({shapeToPy shape}), 0, dtype=np.float32)" -- TODO: make this use actual const
  | .gather _ _ _ _ _ _ => panic! s!"Gather operation not implemented in Python translation"
  | .slice _ _ _ _ => panic! s!"Slice operation not implemented in Python translation"
  | .call _ _ _ =>
    panic! s!"Can't translate call operators to Python"


instance : ToPy Statement where
  toPy p := do
    match p with
    | .comment msg => putLn s!"# {msg}"
    | .assign dest op shape => do
      let opStr := opToPy op
      putLn (s!"{varToPy dest} = {opStr} # {shape}")
      putLn (s!"assert {varToPy dest}.shape == ({shapeToPy shape}), \"Expected %s, got %s\" % (({shapeToPy shape}), {varToPy dest}.shape)")
    | .ret name => putLn (s!"return {varToPy name}")

instance : ToPy Function where
  toPy f := do
    let inputsStr := f.inputs.map (fun shape => s!"\"np.ndarray[({shapeToPy shape})]\"") |> ", ".intercalate |> fun x => s!"args: Tuple[{x}]"
    let outputsStr := f.outputs.map shapeToPy |> ", ".intercalate
    let funcHeader := s!"def {f.name}({inputsStr}) -> (\"np.ndarray[({outputsStr})]\"):"
    let args := f.inputs.map (fun shape => s!"np.zeros(({shapeToPy shape}), dtype=np.float32)")
    let funCall := s!"{f.name}({", ".intercalate args})"
    putLn funcHeader
    increaseIndent
    for statement in f.statements do
      ToPy.toPy statement
    decreaseIndent
    putLn funCall

instance : ToPy Program where
  toPy p := do
    putLn "import numpy as np"
    for func in p.functions do
      ToPy.toPy func

def formatProgram (p : Program) : String :=
  let ctx := FormatCtx.mk 0 ""
  let result := ToPy.toPy p
  match result.run ctx with
  | .ok _ ctx => ctx.program
  | .error err _ => s!"Error formatting program: {err}"

end KLR.HLR
