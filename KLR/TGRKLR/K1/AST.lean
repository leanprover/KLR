import Lean
import TensorLib.Tensor
import KLR.TGR.AST
import KLR.TGRKLR.Operators
import KLR.TGRKLR.Common
import KLR.Core

namespace KLR.TGRKLR.K1

open KLR.TGR(TensorTy)

abbrev Var := String

structure Reg where
  reg : Nat
deriving Inhabited, Repr, BEq, Hashable

structure HbmTensor where
  name : String
deriving Inhabited, Repr, BEq

abbrev TensorK1 := Core.TensorSram

inductive ScalarK1
  | float (f : Float32)
  | int (f : Nat)
  | reg (reg : Reg)
  | address (memory : Core.SramMemory) (parOffset : Core.ParQuadrant) (freeOffset : Nat)
deriving Inhabited, Repr, BEq

inductive RegOp where
  | imm (imm : ScalarK1)
  | add (a b : ScalarK1)
  | mult (a b : ScalarK1)
deriving Inhabited, Repr, BEq

abbrev OperatorK1 := KLR.TGRKLR.Operator TensorK1 ScalarK1

abbrev HbmLocationK1 := KLR.TGRKLR.HbmLocation ScalarK1

inductive StatementK1 where
| comment (s : String)
| op (op : OperatorK1)
| loop (reg : Reg) (start : Nat) (stop : Nat) (step : Nat) (body : List StatementK1)
| ifzero (reg : Reg) (consequent alternate : List StatementK1)
| load (dst : TensorK1) (src : HbmLocationK1)
| store (dst : HbmLocationK1) (src : TensorK1)
| dramToDram (dst : HbmLocationK1) (src : HbmLocationK1)
| move (reg : Reg) (op : RegOp)
deriving Repr, BEq

structure ProgramK1 where
  name : String
  tensors : List (Var × TensorTy)
  inputs : List (Var × TensorTy)
  outputs : List Var
  statements : List StatementK1

instance : ToString HbmTensor where
  toString t := s!"HbmTensor({t.name})"

instance : ToString TensorK1 where
  toString t :=
    let nameStr := if t.name.isEmpty then "" else s!"name: {t.name}, "
    s!"{t.memory}Tile[{t.dtype}]({nameStr}parShape: [{t.parQuadrant}:{t.parQuadrant}+{t.parDim}], freeShape: {t.freeOffset}+{repr t.freePattern})"

instance : ToString Reg where
  toString r := s!"%{r.reg}"

instance : ToString ScalarK1 where
  toString
  | .float f => s!"{f}"
  | .int i => s!"{i}"
  | .reg reg => s!"{reg}"
  | .address memory parOffset freeOffset => s!"{memory}({parOffset},{freeOffset})"

instance : ToString RegOp where
  toString
  | .imm imm => s!"{imm}"
  | .add a b => s!"{a} + {b}"
  | .mult a b => s!"{a} * {b}"

open Std.Format

def formatStatementk2 (s : StatementK1) : Std.Format :=
  match s with
  | .comment s => f!"# {s}"
  | .op op => f!"{op}"
  | .loop var start stop step body =>
    let body := joinSep (body.map formatStatementk2) line
    f!"for {var} in [{start}:{stop}:{step}]:" ++ indentD body
  | .ifzero var consequent alternate =>
    let consequentBody := joinSep (consequent.map formatStatementk2) line
    let alternateBody := joinSep (alternate.map formatStatementk2) line
    f!"if {var} == 0:" ++ indentD consequentBody ++ line ++
    f!"else:" ++ indentD alternateBody
  | .load dst src => f!"{dst} <- {src}"
  | .store dst src => f!"{dst} <- {src}"
  | .dramToDram dst src => f!"dramToDram {dst} <- {src}"
  | .move reg op => s!"{reg} = {op}"

instance : ToString StatementK1 where
  toString s := formatStatementk2 s |>.pretty

def formatProgramK1 (f : ProgramK1) : Std.Format :=
  let tensors := joinSep (f.tensors.map (fun (name, shape) => f!"{name}({shape})")) ","
  let inputs := joinSep (f.inputs.map (fun (name, shape) => f!"{name}({shape})")) ","
  let outputs := joinSep (f.outputs.map ToString.toString) ","
  let body := joinSep (f.statements.map formatStatementk2) line
  f!"def {f.name}({inputs}) -> {outputs} :" ++ indentD tensors ++ line ++ indentD body

instance : ToString ProgramK1 where
  toString f := formatProgramK1 f |>.pretty
