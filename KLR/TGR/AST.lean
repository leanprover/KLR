/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.Util
import SHerLOC
import TensorLib.Dtype
import TensorLib.Shape
import TensorLib.Slice
import TensorLib.Tensor

open TensorLib (Tensor Shape Dtype Slice)

/-
The definition of the Tensor Graph Representation (TGR) IR. The goal of this IR is to
be a uniform representation for graphs of tensor operations, which we can use as a
common compilation target for different frontends (e.g. StableHLO, PyTorch FX, etc.).
A TGR program consists of a list of functions, each with a name, and input and output tensors.
The function body is in SSA, with each operation producing a single output tensor.
-/
namespace KLR.TGR

structure TensorTy where
  shape : Shape
  dtype : Dtype
deriving Inhabited, Repr, Nonempty

abbrev Var := String

/- scalar-scalar binary operators -/
inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | and
  | max
  | cmp
deriving Inhabited, Repr

/- scalar unary operators -/
inductive UnaryOp where
  | exp
  | sqrt
  | neg
  | convert (dtype : Dtype)
deriving Inhabited, Repr

/-
Operators in the TGR (Tensor Graph Representation) IR.

Note: some HLO operations have "load-bearing" output shapes, meaning the
output shape is a vital part of the operation's semantics (e.g. `reshape`).
For these operators, we store the output shape in the `Operator`, even
though this means that when considering an `Operator` as part of a `Statement`,
the output shape information exists in two redundant places: in the `Statement`
and in the `Operator`.
-/
inductive Operator where
  /- An argument to the function, identified by its index. -/
  | arg (index : Nat)

  /- apply a binary operator element-wise to two tensors -/
  | binaryOp (op : BinaryOp) (a b : Var)
  /- apply a unary operator element-wise to a tensor -/
  | unaryOp (op : UnaryOp) (a : Var)
  /- apply a reduction operation to a tensor, reducing it along the specified dimensions -/
  | reductionOp (op : BinaryOp) (a b : Var) (dim : List Nat)

  /- perform a batch matrix multiplication on two tensors.
  Specifically, computes the einsum bij,bkj->bik -/
  | batchMatmul (a b : Var)
  /- create a tensor with a range of values within the given limits and with the specified stride -/
  | arange (start : Nat) (stop : Nat) (step : Nat) (shape : Shape)
  /- concatenate a list of tensors along the specified dimension -/
  | concat (tensors : List Var) (dim : Nat)
  /- select elements from two tensors based on a condition tensor -/
  | select (cond a b : Var)
  /- create a tensor filled with a specific value, with the given shape
  Note: the tensor is always a scalar-array -/
  | full (value : Tensor) (shape : Shape)
  /- transpose a tensor with the provided permutation of dimensions -/
  | transpose (a : Var) (dims : List Nat)
  /- reshape a tensor to the specified shape -/
  | reshape (a : Var) (shape : Shape)
  /-
    broadcast a tensor to the specified shape

    It must be the case that `len(shape(a)) = len(shape)` and that
    `∀ i, shape(a)[i] != shape[i] => shape(a)[i] == 1`
    In other words, the broadcast cannot produce new dimensions, only expand
    existing ones of size 1.
  -/
  | broadcast (a : Var) (shape : Shape)
  /- create a constant tensor with the given values and shape -/
  | const (values : Tensor) (shape : Shape) (dtype : Dtype)
  /- gather elements from a tensor using the provided indices and offset dimensions
  TODO: gather is complicated and not used except for in llama, so for now
  we just pass through the semantics of HLO's gather -/
  | gather (input indices : Var) (offsetDims collapsedSliceDims startIndexMap : List Nat) (indexVectorDim : Nat)
  /- slice a tensor along specified dimensions, with start, limit, and stride -/
  | slice (a : Var) (slice : List Slice)
  /- call another function, passing input values and receiving outputs -/
  | call (callee : String) (inputValues : List Var)
deriving Inhabited, Repr

/-
A statement in TGR (Tensor Graph Representation).
In SSA form, so each variable is assigned exactly once.
-/
inductive Statement where
  /- A comment in the code, for making the dumped IR readable -/
  | comment (msg : String)
  /-
  Assign the result of `op` to `dest` , with resulting shape `shape`

  Note: We store the shape directly, even though it is inferrable based on the,
  operator, to avoid having to recompute it with fallible operations later.
  -/
  | assign (dest : Var) (op : Operator) (shape : TensorTy)
  /- Return variables `vars` from the function -/
  | ret (vars : List Var)
deriving Inhabited, Repr

/-
An TGR function. Note that arguments are referred to by index, so
we only store the argument shapes, not names.
-/
structure Function where
  name : String
  inputs : List TensorTy
  outputs : List TensorTy
  statements : List Statement
deriving Inhabited, Repr, Nonempty

/- A TGR program -/
structure Program where
  functions : List Function
deriving Inhabited, Repr, Nonempty

/- Returns the list of variables that this operator immediately depends on. -/
def dependencies : Operator → List Var
  | .arg _ => []
  | .binaryOp _ a b => [a, b]
  | .unaryOp _ a => [a]
  | .reductionOp _ a b _ => [a, b]
  | .batchMatmul a b => [a, b]
  | .arange .. => []
  | .concat tensors _ => tensors
  | .select cond a b => [cond, a, b]
  | .full .. => []
  | .transpose a _ => [a]
  | .reshape a _ => [a]
  | .broadcast a .. => [a]
  | .const .. => []
  | .gather a i .. => [a, i]
  | .slice a .. => [a]
  | .call _ inputs => inputs

/- Returns the list of all variables defined in this function. -/
def vars (f : Function) : List Var :=
  f.statements.filterMap (fun
    | .assign dest .. => .some dest
    | _ => .none)

/- Finds the operator that assigns to a variable in the function. -/
def findVar (f : Function) (v : Var) : Option Operator :=
  f.statements.findSome? (fun
    | .assign dest op _ => if dest == v then .some op else .none
    | _ => .none)

/- TODO: move these toString instances to the TensorLib repo -/
instance : ToString Slice where
  toString s :=
    let {start, stop, step, ..} := s
    let start := start.map toString |>.getD ""
    let stop := stop.map toString |>.getD ""
    let step := step.map toString |>.getD ""
    s!"{start}:{stop}:{step}"

instance : ToString Shape where
  toString s :=
    s.val.map toString |> "x".intercalate |> fun x => s!"[{x}]"

instance : ToString Dtype where
  toString
    | .bool => "bool"
    | .int8 => "i8"
    | .int16 => "i16"
    | .int32 => "i32"
    | .int64 => "i64"
    | .uint8 => "u8"
    | .uint16 => "u16"
    | .uint32 => "u32"
    | .uint64 => "u64"
    | .float32 => "f32"
    | .float64 => "f64"

instance : ToString BinaryOp where
  toString
    | .add => "add"
    | .sub => "sub"
    | .mul => "mul"
    | .div => "div"
    | .and => "and"
    | .max => "max"
    | .cmp => "cmp"

instance : ToString UnaryOp where
  toString
    | .exp => "exp"
    | .sqrt => "sqrt"
    | .neg => "neg"
    | .convert dtype => s!"convert_{dtype}"

instance : ToString TensorTy where
  toString (t : TensorTy) : String :=
    s!"{t.shape}{t.dtype}"

instance : ToString Operator where
  toString
    | .arg n => s!"arg({n})"
    | .binaryOp binOp a b => s!"{binOp}({a}, {b})"
    | .unaryOp unOp a => s!"{unOp}({a})"
    | .reductionOp redOp a b dim => s!"reduce-{redOp}({a}, {b}, dim={dim})"
    | .batchMatmul a b => s!"matmul({a}, {b})"
    | .arange start stop step shape => s!"arange({start}, {stop}, {step}, shape={shape})"
    | .concat tensors dim => s!"concat({", ".intercalate tensors}, dim={dim})"
    | .select cond a b => s!"select({cond}, {a}, {b})"
    | .full v shape => s!"full({repr v}, shape={shape})"
    | .transpose a dims => s!"transpose({a}, dims={dims})"
    | .reshape a shape => s!"reshape({a}, shape={shape})"
    | .broadcast a shape => s!"broadcast({a}, shape={shape})"
    | .const t shape dtype => s!"const({repr t}, shape={shape}, dtype={dtype})"
    | .gather a indices offsetDims collapsedSliceDims startIndexMap indexVectorDim
      => s!" gather({a}, indices={indices}, offsetDims={offsetDims}, collapsedSliceDims={collapsedSliceDims}, startIndexMap={startIndexMap}, indexVectorDim={indexVectorDim})"
    | .slice a slices => s!"slice({a}, {slices})"
    | .call callee inputValues =>
      let inputsStr := inputValues.map toString |> ", ".intercalate
      s!"call({callee}, inputs=[{inputsStr}])"

instance : ToString Statement where
  toString
    | .comment msg => s!"# {msg}"
    | .assign dest op shape => s!"{dest} : {toString shape} = {op}"
    | .ret name => s!"return {name}"

instance : ToString Function where
  toString f :=
    let inputsStr := f.inputs.map toString |> ", ".intercalate
    let outputsStr := f.outputs.map toString |> ", ".intercalate
    let statementsStr := f.statements.map toString |> "\n".intercalate
    s!"def {f.name}({inputsStr}) -> ({outputsStr}):\n{statementsStr}"

instance : ToString Program where
  toString p :=
    let functionsStr := p.functions.map toString |> "\n".intercalate
    s!"# Program\n" ++ functionsStr

/- Human readable name for the operator. -/
def opName : Operator → String
  | .arg _ => s!"arg"
  | .binaryOp binOp .. => s!"{binOp}"
  | .unaryOp unOp .. => s!"{unOp}"
  | .reductionOp redOp .. => s!"{redOp}"
  | .batchMatmul .. => s!"batchMatmul"
  | .arange .. => s!"arange"
  | .concat .. => s!"concat"
  | .select .. => s!"select"
  | .full .. => s!"full"
  | .transpose .. => s!"transpose"
  | .reshape .. => s!"reshape"
  | .broadcast .. => s!"broadcast"
  | .const .. => s!"const"
  | .gather .. => s!"gather"
  | .slice .. => s!"slice"
  | .call callee .. => s!"call {callee}"

end KLR.TGR
