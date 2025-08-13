import Lean
import TensorLib.Tensor
import KLR.TGR.AST
import KLR.TGRKLR.Operators
import KLR.TGRKLR.Common
import KLR.Core

namespace KLR.TGRKLR.K2

open KLR.TGR(TensorTy)

abbrev Var := String
abbrev ScalarVar := String

structure HbmTensor where
  name : String
deriving Inhabited, Repr, BEq

structure TensorK2 where
  name    : String
  dtype   : Core.Dtype
  memory : Core.SramMemory
  -- The size of this tensor in the parallel dimension
  parDim : Nat
  -- The length and stride of each dimension besides the first
  freePattern: List Core.APPair
deriving BEq, Repr

inductive ScalarOp where
  | mult
  | add
deriving Inhabited, Repr, BEq

inductive ScalarK2
  | float (f : Float32)
  | int (f : Nat)
  | var (var : ScalarVar)
  | expr (op : ScalarOp) (a b : ScalarK2)
  | address (name : Var)
deriving Inhabited, Repr, BEq

abbrev OperatorK2 := KLR.TGRKLR.Operator TensorK2 ScalarK2

abbrev HbmLocationK2 := KLR.TGRKLR.HbmLocation ScalarK2

inductive StatementK2 where
| comment (s : String)
| op (op : OperatorK2)
| loop (var : ScalarVar) (start : Nat) (stop : Nat) (step : Nat) (body : List StatementK2)
| ifzero (var : ScalarVar) (consequent alternate : List StatementK2)
| load (dst : TensorK2) (src : HbmLocationK2)
| store (dst : HbmLocationK2) (src : TensorK2)
| dramToDram (dst : HbmLocationK2) (src : HbmLocationK2)
| assign (var : ScalarVar) (expr : ScalarK2)

structure ProgramK2 where
  name : String
  tensors : List (Var × TensorTy)
  inputs : List (Var × TensorTy)
  outputs : List Var
  statements : List StatementK2

instance : ToString HbmTensor where
  toString t := s!"HbmTensor({t.name})"

instance : ToString TensorK2 where
  toString t :=
    s!"{t.memory}Tile[{t.dtype}]({t.name}, parSize: {t.parDim}, freeShape: {repr t.freePattern})"

def toStringScalarK2 : ScalarK2 → String
  | .float f => s!"{f}"
  | .int i => s!"{i}"
  | .var var => s!"%{var}"
  | .expr op a b =>
    let opStr := match op with
      | .mult => "*"
      | .add => "+"
    s!"({toStringScalarK2 a} {opStr} {toStringScalarK2 b})"
  | .address name => s!"{name}"
instance : ToString ScalarK2 := ⟨toStringScalarK2⟩

open Std.Format

def formatStatementk2 (s : StatementK2) : Std.Format :=
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
  | .assign var expr => f! "let {var} = {expr}"

instance : ToString StatementK2 where
  toString s := formatStatementk2 s |>.pretty

def formatProgramK2 (f : ProgramK2) : Std.Format :=
  let tensors := joinSep (f.tensors.map (fun (name, shape) => f!"{name}({shape})")) ","
  let inputs := joinSep (f.inputs.map (fun (name, shape) => f!"{name}({shape})")) ","
  let outputs := joinSep (f.outputs.map ToString.toString) ","
  let body := joinSep (f.statements.map formatStatementk2) line
  f!"def {f.name}({inputs}) -> {outputs} :" ++ indentD tensors ++ line ++ indentD body

instance : ToString ProgramK2 where
  toString f := formatProgramK2 f |>.pretty
