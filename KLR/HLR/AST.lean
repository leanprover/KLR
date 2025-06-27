/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.Util
import SHerLOC
import TensorLib.Shape
import TensorLib.Slice
import TensorLib.Dtype

namespace KLR.HLR

abbrev Shape := TensorLib.Shape
structure TensorTy where
  shape : TensorLib.Shape
  dtype : TensorLib.Dtype
deriving Inhabited, Repr, Nonempty

abbrev Var := String

-- scalar-scalar binary operators
inductive BinaryOp where
  | mul
  | max
  | sub
  | add
  | div
  | cmp
  | and
deriving Inhabited, Repr

-- scalar unary operators
inductive UnaryOp where
  | exp
  | sqrt
  | neg
  | convert
deriving Inhabited, Repr

-- Operators in the HLR (High-Level Representation) of KLR.
inductive Operator where
  -- An argument to the function, identified by its index.
  | arg (index : Nat)

  -- apply a binary operator element-wise to two tensors
  | binaryOp (op : BinaryOp) (a b : Var)
  -- apply a unary operator element-wise to a tensor
  | unaryOp (op : UnaryOp) (a : Var)
  -- apply a reduction operation to a tensor, reducing it along the specified dimensions
  | reductionOp (op : BinaryOp) (a b : Var) (dim : List Nat)

  -- perform a batch matrix multiplication on two tensors.
  -- Specifically, computes the einsum bij,bkj->bik
  | batchMatmul (a b : Var)
  -- create a tensor with a range of values within the given limits and with the specified stride
  | arange (start : Nat) (stop : Nat) (step : Nat) (shape : Shape)
  -- concatenate a list of tensors along the specified dimension
  | concat (tensors : List Var) (dim : Nat)
  -- select elements from two tensors based on a condition tensor
  | select (cond a b : Var)
  -- create a tensor filled with a specific value, with the given shape
  | full (value : StableHLO.Parsing.FloatLiteral) (shape : Shape)
  -- transpose a tensor with the provided permutation of dimensions
  | transpose (a : Var) (dims : List Nat)
  -- unused
  | split_with_sizes (a : Var) (sizes : List Nat) -- ??
  -- reshape a tensor to the specified shape
  | reshape (a : Var) (shape : Shape)
  -- broadcast a tensor to the specified shape
  | broadcast (a : Var) (shape : Shape)
  -- create a constant tensor with the given values and shape
  | const (values : StableHLO.Parsing.DenseLiteral) (shape : Shape) (dtype : TensorLib.Dtype)
  -- gather elements from a tensor using the provided indices and offset dimensions
  | gather (input indices : Var) (offsetDims collapsedSliceDims startIndexMap : List Nat) (indexVectorDim : Nat)
  -- slice a tensor along specified dimensions, with start, limit, and stride
  | slice (a : Var) (start limit stride : List Nat)
  -- call another function, passing input values and receiving outputs
  | call (callee : String) (inputValues : List Var)
deriving Inhabited, Repr

-- A statement in the HLR, which can be a comment, an assignment, or a return statement.
-- In SSA form, so each variable is assigned exactly once.
inductive Statement where
  -- a comment in the code, for documentation purposes
  | comment (msg : String)
  -- assign the result of an operator to a fresh variable, with the specified shape
  | assign (dest : Var) (op : Operator) (shape : TensorTy)
  -- return a variable from the function
  | ret (name : Var)
deriving Inhabited, Repr

-- A function in the HLR, which consists of a name, input shapes, output shapes, and a list of statements.
structure Function where
  name : String
  inputs : List TensorTy
  outputs : List TensorTy
  statements : List Statement
deriving Inhabited, Repr, Nonempty

structure Program where
  functions : List Function
deriving Inhabited, Repr, Nonempty

instance : Coe StableHLO.Parsing.TensorType TensorTy where
  coe (t : StableHLO.Parsing.TensorType) :=
    let (shape : Shape) := t.shape.map (fun dim => match dim with
      | .known d =>  d
      | .unknown => panic! "Can't support tensors with unkown shape") |> .mk
    let (dtype : TensorLib.Dtype) := match t.tensorElementTypeGen with
      | .classic (.floatType .f32) => TensorLib.Dtype.float32
      | _ => panic! s!"Unsupported tensor element type: {repr t.tensorElementTypeGen}"
    .mk shape dtype


instance : ToString BinaryOp where
  toString op :=
    match op with
    | .mul => "mul"
    | .max => "max"
    | .sub => "sub"
    | .add => "add"
    | .div => "div"
    | .cmp => "cmp"
    | .and => "and"
instance : ToString UnaryOp where
  toString op :=
    match op with
    | .exp => "exp"
    | .sqrt => "sqrt"
    | .neg => "neg"
    | .convert => "convert"
instance : ToString TensorTy where
  toString (t : TensorTy) : String :=
    s!"{t.shape}x{t.dtype}"

def opName (op : Operator) : String :=
  match op with
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
  | .split_with_sizes .. => s!"split_with_sizes"
  | .reshape .. => s!"reshape"
  | .broadcast .. => s!"broadcast"
  | .const .. => s!"const"
  | .gather .. => s!"gather"
  | .slice .. => s!"slice"
  | .call callee .. => s!"call {callee}"

-- Returns the list of variables that this operator immediately depends on.
def dependencies (op : Operator) : List Var :=
  match op with
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
  | .split_with_sizes a _ => [a]
  | .reshape a _ => [a]
  | .broadcast a _ => [a]
  | .const .. => []
  | .gather a i .. => [a, i]
  | .slice a .. => [a]
  | .call _ inputs => inputs

-- Returns the list of all variables in this function.
def vars (f : Function) : List Var :=
  f.statements.filterMap (fun stmt =>
    match stmt with
    | .assign dest .. => .some dest
    | _ => .none)

-- Finds the operator that assigns to a variable in the function.
def findVar (f : Function) (v : Var) : Option Operator :=
  f.statements.findSome? (fun stmt =>
    match stmt with
    | .assign dest op _ => if dest == v then .some op else .none
    | _ => .none)

-- Finds the statement that assigns to a variable in the function.
def transitiveDependencies (f : Function) (v : Var) : List Var := Id.run do
  let mut deps := [v]
  repeat
    let newDeps := deps.flatMap (fun v => match findVar f v with
      | .some x => dependencies x
      | .none => [])
    let filtered := newDeps.filter (fun s => ! deps.contains s)
    if filtered.isEmpty then
      break
    deps := deps ++ filtered
  return deps

def forwardEdges (f : Function) : List (Var × List Var) := Id.run do
  let mut edges := (vars f).map fun v => (v, [])
  for stmt in f.statements do
    match stmt with
    | .assign dest op _ =>
      let deps := dependencies op
      for dep in deps do
        edges := edges.map (fun (v, es) => if v == dep then (v, es ++ [dest]) else (v, es))
    | _ => ()
  return edges

def topoSort (f : Function) : List Var := Id.run do
  -- kahn's algorithm for topological sorting
  let mut sorted := []
  -- nodes with no incoming edges
  let mut queue := vars f |> .filter (fun v =>
    match findVar f v with
    | .some (.arg _) | .some (.const _ _ _) => true
    | _ => false)
  let mut forwardEdges := forwardEdges f
  while ! queue.isEmpty do
    -- remove a node from the queue
    let n := queue.head!
    queue := queue.tail!
    -- add it to the sorted list
    sorted := sorted ++ [n]

    -- find all edges that start from this node
    let dests := forwardEdges.findSome? (fun (v, es) => if v == n then .some es else .none)
    match dests with
      | .some es =>
      -- for each edge:
      for e in es do
        -- remove the edge from the graph
        forwardEdges := forwardEdges.map (fun (v, es) => (v, es.filter (fun x => x != e)))
        -- if the destination has no other incoming edges, add it to the queue
        if ! forwardEdges.any (fun (_, deps) => deps.contains e) then
          queue := queue ++ [e]
      | none => ()
  if forwardEdges.any (fun (_, deps) => ! deps.isEmpty) then
    panic! "Graph has cycles, cannot perform topological sort"
  return sorted


end KLR.HLR
