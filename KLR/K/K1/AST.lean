import KLR.Core
import KLR.TGR.AST
import KLR.K.Common
import KLR.K.Operators
import Lean
import TensorLib.Tensor

open KLR.TGR(TensorTy)

namespace KLR.K.K1

/- in K1:

* tile names and hbm tensor names are globally unique
* patterns have their slowest moving dimension first (matches numpy)
* patterns are in terms of number of elements, not bytes
* offsets are in terms of bytes, not elements
-/

abbrev Var := String

/- A register is simply a natural number (maps to hardware) -/
structure Reg where
  reg : Nat
deriving Inhabited, Repr, BEq, Hashable

/- We can address tensors in HBM simply by their name -/
structure HbmTensor where
  name : String
deriving Inhabited, Repr, BEq

inductive SramMemory where
  | sbuf
  | psum
  | unknown
deriving BEq, Repr
instance : ToString SramMemory where
  toString
    | .sbuf => "Sbuf"
    | .psum => "Psum"
    | .unknown => "Unknown"

/- Tensors in K1 have a physical location as well as a size -/
structure TensorK1 where
  name : String
  dtype : Core.Dtype
  memory : SramMemory
  -- The size of this tensor in the parallel dimension
  parNum : Nat
  -- The length and stride of each dimension besides the first
  freePattern: List Core.APPair
  -- Which parallel dimension channel this tensor starts at
  parOffset : Nat := 0
  -- The offset in the partition channel of this tensor
  freeOffset : Nat := 0
  deriving BEq, Repr


/- The scalars that are passed to instructions can be floats, ints, addresses, or an address stored
in a register (pointer). -/
inductive ScalarK1
  | float (f : Float32)
  | int (f : Nat)
  | reg (reg : Reg)
  | address (memory : SramMemory) (parOffset : Nat) (freeOffset : Nat)
deriving Inhabited, Repr, BEq

/- The set of operations we can do on a register -/
inductive RegOp where
  | imm (imm : ScalarK1)
  | add (a b : ScalarK1)
  | mult (a b : ScalarK1)
deriving Inhabited, Repr, BEq

abbrev OperatorK1 := KLR.K.Operator TensorK1 ScalarK1

/- Note that offset is in terms of number of bytes, but pattern is in terms of number of elements of size `dtype`. -/
abbrev HbmLocationK1 := KLR.K.HbmLocation ScalarK1

inductive StatementK1 where
  | comment (s : String)
  /- Run an operator for its side effects -/
  | op (op : OperatorK1)
  /- Repeat `body`, incrementing register `reg` from `start` to `stop` by `step`. -/
  | loop (reg : Reg) (start : Nat) (stop : Nat) (step : Nat) (body : List StatementK1)
  /- If `reg` is zero, run `consequent`, otherwise run `alternate` -/
  | ifzero (reg : Reg) (consequent alternate : List StatementK1)

  /-
  Note that in load and store, the field `TensorK1.freeOffset` is in terms of
  bytes into the free dimension, but `TensorK1.freePattern` is in terms of
  number of elements of size `dtype`.
  -/
  | load (dst : TensorK1) (src : HbmLocationK1)
  | store (dst : HbmLocationK1) (src : TensorK1)
  /- Move data from one HBM address to another -/
  | dramToDram (dst : HbmLocationK1) (src : HbmLocationK1)
  /- Execute a register operation and store the result in `reg` -/
  | move (reg : Reg) (op : RegOp)
deriving Inhabited, Repr, BEq

/- A program in K1 is similar to K2. See there for details. -/
structure ProgramK1 where
  name : String
  tensors : List (Var × TensorTy)
  inputs : List (Var × TensorTy)
  outputs : List Var
  statements : List StatementK1
deriving Inhabited, Repr, BEq

instance : ToString HbmTensor where
  toString t := s!"HbmTensor({t.name})"

instance : ToString TensorK1 where
  toString t :=
    let nameStr := if t.name.isEmpty then "" else s!"name: {t.name}, "
    s!"{t.memory}Tile[{t.dtype}]({nameStr}parShape: [{t.parOffset}:{t.parOffset}+{t.parNum}], freeShape: {t.freeOffset}+{repr t.freePattern})"

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
