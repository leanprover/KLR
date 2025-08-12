import Lean
import TensorLib.Tensor
import KLR.TGR.AST
import KLR.TGRKLR.Operators

namespace KLR.TGRKLR.K2

open KLR.TGR(TensorTy)

abbrev Var := String

structure HbmTensor where
  name : String
deriving Inhabited, Repr, BEq

abbrev TensorK2 := KLR.Core.TensorSram

abbrev Reg := Nat

inductive ScalarOp where
  | mult
  | add
deriving Inhabited, Repr, BEq

inductive ScalarK2
  | float (f : Float32)
  | int (f : Nat)
  | var (var : Reg)
  | expr (op : ScalarOp) (a b : ScalarK2)
deriving Inhabited, Repr, BEq

abbrev OperatorK2 := KLR.TGRKLR.Operator TensorK2 ScalarK2

mutual
  inductive HbmLocation where
  | mk (name : String) (offset : ScalarK2) (pattern : List Core.APPair)

  inductive StatementK2 where
  | comment (s : String)
  | op (op : OperatorK2)
  | loop (var : Reg) (start : Nat) (stop : Nat) (step : Nat) (body : List StatementK2)
  | ifzero (var : Reg) (consequent alternate : List StatementK2)
  | load (dst : TensorK2) (src : HbmLocation)
  | store (dst : HbmLocation) (src : TensorK2)
  | dramToDram (dst : HbmLocation) (src : HbmLocation)
  | move (reg : Reg) (expr : ScalarK2)
  | moveAddress (reg : Reg) (parOffset : Core.ParQuadrant) (freeOffset : Nat)
end

structure FunctionK2 where
  name : String
  tensors : List (Var × TensorTy)
  inputs : List (Var × TensorTy)
  outputs : List Var
  statements : List StatementK2

structure ProgramK2 where
  functions : List FunctionK2

instance : ToString HbmTensor where
  toString t := s!"HbmTensor({t.name})"

instance : ToString TensorK2 where
  toString t :=
    let nameStr := if t.name.isEmpty then "" else s!"name: {t.name}, "
    s!"{t.memory}Tile[{t.dtype}]({nameStr}parShape: [{t.parQuadrant}:{t.parQuadrant}+{t.parDim}], freeShape: {t.freeOffset}+{repr t.freePattern})"

def toStringScalarK2 : ScalarK2 → String
  | .float f => s!"{f}"
  | .int i => s!"{i}"
  | .var var => s!"%{var}"
  | .expr op a b =>
    let opStr := match op with
      | .mult => "*"
      | .add => "+"
    s!"({toStringScalarK2 a} {opStr} {toStringScalarK2 b})"
instance : ToString ScalarK2 := ⟨toStringScalarK2⟩

instance : ToString HbmLocation where
  toString
  | .mk name offset pattern => s!"HbmLoc(at: {name}[{offset}], pattern: {repr pattern})"

open Std.Format

def formatStatementk2 (s : StatementK2) : Std.Format :=
  match s with
  | .comment s => f!"# {s}"
  | .op op => f!"{op}"
  | .loop var start stop step body =>
    let body := joinSep (body.map formatStatementk2) line
    f!"for {var} in [{start}, {stop}, {step}]:" ++ indentD body
  | .ifzero var consequent alternate =>
    let consequentBody := joinSep (consequent.map formatStatementk2) line
    let alternateBody := joinSep (alternate.map formatStatementk2) line
    f!"if {var} == 0:" ++ indentD consequentBody ++ line ++
    f!"else:" ++ indentD alternateBody
  | .load dst src => f!"{dst} <- {src}"
  | .store dst src => f!"{dst} <- {src}"
  | .dramToDram dst src => f!"dramToDram {dst} <- {src}"
  | .move reg expr => f! "%{reg} = {expr}"
  | .moveAddress reg parOffset freeOffset => f! "%{reg} = {repr parOffset} + {freeOffset}"

instance : ToString StatementK2 where
  toString s := formatStatementk2 s |>.pretty

def formatFunctionK2 (f : FunctionK2) : Std.Format :=
  let tensors := joinSep (f.tensors.map (fun (name, shape) => f!"{name}({shape})")) ","
  let inputs := joinSep (f.inputs.map (fun (name, shape) => f!"{name}({shape})")) ","
  let outputs := joinSep (f.outputs.map ToString.toString) ","
  let body := joinSep (f.statements.map formatStatementk2) line
  f!"def {f.name}({inputs}) -> {outputs} :" ++ indentD tensors ++ line ++ indentD body

instance : ToString FunctionK2 where
  toString f := formatFunctionK2 f |>.pretty
