/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.TGR.AST
import SHerLOC.Analysis.Graph

open StableHLO.Analysis (Graph Edge Vertex)

-- This module provides a way to convert an TGR function into a DOT graph representation.
namespace KLR.TGR.Graph

/-
Process the name `var` so that it can used as a node ID in DOT format.
Notably, IDs can't start with a digit, so we prefix it with "node_".
-/
def sanitize (var : String) : String :=
  s!"node_{var}"

def makeReturnNode (funcName : String) : Vertex :=
  .mk
    s!"return_{funcName}"
    (.mk [
      ("label", s!"return\\n{funcName}"),
      ("shape", "box"),
      ("style", "filled"),
      ("fillcolor", "lightgray"),
      ("color", "gray")
    ])
def makeOpNode (op : Operator) (output : String) (ty : KLR.TGR.TensorTy): Vertex :=
  let attrs := match op with
  | .arg .. => [
      ("shape", "diamond"),
      ("style", "filled"),
      ("fillcolor", "lightgreen"),
      ("color", "green")
    ]
  | .batchMatmul .. => [
      ("style", "filled"),
      ("fillcolor", "lightpink"),
      ("color", "red")
    ]
  | .slice .. => [
      ("style", "filled"),
      ("fillcolor", "lightblue"),
      ("color", "blue")
    ]
  | _ => []
  .mk
    (sanitize output)
    (.mk ([
      ("label", s!"{opName op}\\n{output}\n{ty.shape}"),
    ] ++ attrs))

def makeConstNode (name : String) (usedAt : String): Vertex :=
  .mk
    s!"node_const_{name}_{usedAt}"
    (.mk [
      ("label", s!"const\\n{name} ({usedAt})"),
      ("shape", "diamond"),
      ("style", "filled"),
      ("fillcolor", "lightyellow"),
      ("color", "yellow")
    ])

def makeEdge (source : String) (dest : String) : Edge :=
  .mk
    source
    dest
    (.mk [])

/-
Convert an TGR function to a DOT graph, where each variable is a vertex
and an edge exists from A to B if A is used in the computation of B.

Note: since constants are reused in many parts of the function, they can
cause the graph to have long edges that cross over other nodes. To avoid this,
we create a separate vertex for each use of a constant.
-/
def graph (f : TGR.Function) : Graph := Id.run do
  let mut vertices := []
  let mut edges := []
  -- Every variables in the function that is the result of a `constant` operatior
  let mut consts := f.statements.filterMap (fun
    | .assign v (.const _ _ _) _ => .some v
    | _ => .none)
  -- A closure that creates edges from a list of inputs to an output variable.
  -- If the input is a constant, it creates a vertex for that constant.
  let (makeEdges : List String → String → (List Vertex) × (List Edge)) := fun inputs output => Id.run do
    let mut vertices := []
    let mut edges := []
    for input in inputs do
      if consts.contains input then
        let node := makeConstNode input output
        vertices := node :: vertices
        edges := (makeEdge node.id output) :: edges
      else
        edges := (makeEdge input output) :: edges
    return (vertices, edges)

  -- Walk the program statements and create vertices and edges.
  for s in f.statements do
    match s with
    | .assign _ (.const _ _ _) _ => ()
    | .assign v op ty =>
      let deps := dependencies op |>.map sanitize
      let (newVertices, newEdges) := makeEdges deps (sanitize v)
      vertices := [makeOpNode op v ty] ++ newVertices ++ vertices
      edges := newEdges ++ edges
    | .ret vars =>
      let node := makeReturnNode f.name
      let deps := vars.map sanitize
      let (newVertices, newEdges) := makeEdges deps node.id
      vertices := [node] ++ newVertices ++ vertices
      edges := newEdges ++ edges
    | .comment _ => ()

  .mk f.name vertices edges

end KLR.TGR.Graph
