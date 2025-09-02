import KLR.Core
import KLR.TGR.AST
import KLR.K.Common
import KLR.K.Operators
import KLR.K.K1.AST
import Lean
import TensorLib.Tensor

namespace KLR.K.K2

open KLR.TGR(TensorTy)

/- Variables that represent a location in SBUF/PSUM -/
abbrev Var := String
/- Variables that have been bound by a let expression -/
abbrev ScalarVar := String

/- We assume HBM tensors can be referred to by name and tensors with different
names do not overlap. -/
structure HbmTensor where
  name : String
deriving Inhabited, Repr, BEq

/- A tile in SBUF/PSUM that has a size in the parallel and free dimension.

Note that at the K2 level, the tile has not had a specific location allocated yet.
The name stands in for the location, and we assume tiles with the same name
are at an identical location and tiles with different names do not overlap. -/
structure TensorK2 where
  name    : String
  dtype   : Core.Dtype
  memory : K1.SramMemory
  /- The size of this tensor in the parallel dimension -/
  parNum : Nat
  /- The size and stride of each dimension besides the first.
  Slower-moving dimensions come first. -/
  freePattern: List Core.APPair
deriving BEq, Repr

inductive ScalarOp where
  | mult
  | add
deriving Inhabited, Repr, BEq

/- A scalar in K2, which is an expression in a small expression language. -/
inductive ScalarK2
  | float (f : Float32)
  | int (f : Nat)
  /- Use a scalar variable that has been let-bound by an `assign` statement -/
  | var (var : ScalarVar)
  | expr (op : ScalarOp) (a b : ScalarK2)
  /- Reference an address in SBUF/PSUM (at the K2 level,
  addresses haven't been allocate yet, so we just use a name) -/
  | address (name : Var)
deriving Inhabited, Repr, BEq

abbrev OperatorK2 := KLR.K.Operator TensorK2 ScalarK2

/- An access pattern into a tensor in HBM -/
abbrev HbmLocationK2 := KLR.K.HbmLocation ScalarK2

/- Statements that comprise a K2 program -/
inductive StatementK2 where
  | comment (s : String)
  /- execute a side-effectful operator -/
  | op (op : OperatorK2)
  /- Continue executing body until `var==stop`, incrementing `var` by `step`
  each time and initializing `var` to `start`. -/
  | loop (var : ScalarVar) (start : Nat) (stop : Nat) (step : Nat) (body : List StatementK2)
  /- If `var==0`, execute `consequent`, otherwise execute `alternate`. -/
  | ifzero (var : ScalarVar) (consequent alternate : List StatementK2)
  /- Load a tensor from HBM into SBUF/PSUM -/
  | load (dst : TensorK2) (src : HbmLocationK2)
  /- Store a tensor from SBUF/PSUM into HBM -/
  | store (dst : HbmLocationK2) (src : TensorK2)
  /- Move a tensor from one HBM location to another -/
  | dramToDram (dst : HbmLocationK2) (src : HbmLocationK2)
  /- let-bind a scalar variable to the result of an expression -/
  | assign (var : ScalarVar) (expr : ScalarK2)
deriving Inhabited, Repr, BEq

structure ProgramK2 where
  /- At the moment, this isn't used for anything useful -/
  name : String
  /- The list of intermediate HBM tensors that are written to in the program (but are not inputs). -/
  tensors : List (Var × TensorTy)
  /- The set of HBM tensors that are inputs to the program. Can be referred to by name. -/
  inputs : List (Var × TensorTy)
  /- The set of HBM tensor names that will be written to by the end of the program. Subset of `tensors` -/
  outputs : List Var
  /- A K2 program has no functions, just a list of statements that are executed in order. -/
  statements : List StatementK2
deriving Inhabited, Repr, BEq

instance : ToString HbmTensor where
  toString t := s!"HbmTensor({t.name})"

instance : ToString TensorK2 where
  toString t :=
    s!"{t.memory}Tile[{t.dtype}]({t.name}, parSize: {t.parNum}, freeShape: {repr t.freePattern})"

def toStringScalarK2 : ScalarK2 → String
  | .float f => s!"{f}"
  | .int i => s!"{i}"
  | .var var => s!"{var}"
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
