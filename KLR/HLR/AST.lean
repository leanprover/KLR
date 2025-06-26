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

namespace KLR.HLR
abbrev Shape := TensorLib.Shape
abbrev Var := String

inductive BinaryOp where
  | mul
  | max
  | sub
  | add
  | div
  | cmp
  | and
deriving Inhabited, Repr

inductive UnaryOp where
  | exp
  | sqrt
  | neg
  | convert
deriving Inhabited, Repr

inductive Value where
  | todo
deriving Inhabited, Repr

inductive Operator where
  | arg (index : Nat)

  | binaryOp (op : BinaryOp) (a b : Var)
  | unaryOp (op : UnaryOp) (a : Var)
  | reductionOp (op : BinaryOp) (a b : Var) (dim : List Nat)

  | batchMatmul (a b : Var) (batchDims : Nat)
  | arange (start : Nat) (stop : Nat) (step : Nat) (shape : Shape)
  | concat (tensors : List Var) (dim : Nat)
  | select (cond a b : Var)
  | full (value : StableHLO.Parsing.FloatLiteral) (shape : Shape)
  | transpose (a : Var) (dims : List Nat)
  | split_with_sizes (a : Var) (sizes : List Nat) -- ??
  | reshape (a : Var) (shape : Shape)
  | broadcast (a : Var) (shape : Shape)
  | const (values : StableHLO.Parsing.DenseLiteral) (shape : Shape)
  | gather (input indices : Var) (offsetDims collapsedSliceDims startIndexMap : List Nat) (indexVectorDim : Nat)
  | slice (a : Var) (start limit stride : List Nat)
  | call (callee : String) (inputValues : List Var) (outputs : List Var)
deriving Inhabited, Repr

inductive Statement where
  | comment (msg : String)
  | assign (dest : Var) (op : Operator) (shape : Shape)
  | ret (name : Var)
deriving Inhabited, Repr

structure Function where
  name : String
  inputs : List Shape
  outputs : List Shape
  statements : List Statement
deriving Inhabited, Repr, Nonempty

structure Program where
  functions : List Function
deriving Inhabited, Repr, Nonempty

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

def opName (op : Operator) : String :=
  match op with
  | .arg _ => s!"arg"
  | .binaryOp binOp _ _ => s!"{binOp}"
  | .unaryOp unOp _ => s!"{unOp}"
  | .reductionOp redOp _ _ _ => s!"{redOp}"
  | .batchMatmul _ _ _ => s!"batchMatmul"
  | .arange _ _ _ _ => s!"arange"
  | .concat _ _ => s!"concat"
  | .select _ _ _ => s!"select"
  | .full _ _ => s!"full"
  | .transpose _ _ => s!"transpose"
  | .split_with_sizes _ _ => s!"split_with_sizes"
  | .reshape _ _ => s!"reshape"
  | .broadcast _ _ => s!"broadcast"
  | .const _ _ => s!"const"
  | .gather _ _ _ _ _ _ => s!"gather"
  | .slice _ _ _ _ => s!"slice"
  | .call callee _ _ => s!"call {callee}"

def dependencies (op : Operator) : List Var :=
  match op with
  | .arg _ => []
  | .binaryOp _ a b => [a, b]
  | .unaryOp _ a => [a]
  | .reductionOp _ a b _ => [a, b]
  | .batchMatmul a b _ => [a, b]
  | .arange _ _ _ _ => []
  | .concat tensors _ => tensors
  | .select cond a b => [cond, a, b]
  | .full _ _ => []
  | .transpose a _ => [a]
  | .split_with_sizes a _ => [a]
  | .reshape a _ => [a]
  | .broadcast a _ => [a]
  | .const _ _ => []
  | .gather a i _ _ _ _ => [a, i]
  | .slice a _ _ _ => [a]
  | .call _ inputs outputs => inputs ++ outputs

def vars (f : Function) : List Var :=
  f.statements.filterMap (fun stmt =>
    match stmt with
    | .assign dest _ _ => .some dest
    | _ => .none)

def findVar (f : Function) (v : Var) : Option Operator :=
  f.statements.findSome? (fun stmt =>
    match stmt with
    | .assign dest op _ => if dest == v then .some op else .none
    | _ => .none)

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
    | .some (.arg _) | .some (.const _ _) => true
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
