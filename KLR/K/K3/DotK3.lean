import KLR.K.K3.AST
import SHerLOC.Analysis.Graph

open StableHLO.Analysis (Graph Edge Vertex)

namespace KLR.K.K3

/- This module outputs a K3 program as a graph in DOT format -/

/- DOT identifiers can't start with numbers, so we need to sanitize them -/
def sanitize (var : String) : String :=
  s!"node_{var}"

/- Makes a graph node for an argument to the kernel -/
def makeArgNode (argName : String) : Vertex :=
  .mk
    (sanitize argName)
    (.mk [
      ("label", s!"arg\\n{argName}"),
      ("shape", "box"),
      ("style", "filled"),
      ("fillcolor", "lightgray"),
      ("color", "gray")
    ])

/- Makes a graph node for an operator, with the output tensor as the label -/
def makeOpNode (op : OperatorK3) (output : TensorK3) : Vertex :=
  let attrs := match op with
  | .matmulP .. => [
      ("style", "filled"),
      ("fillcolor", "lightpink"),
      ("color", "red")
    ]
  | _ => []
  .mk
    (sanitize output.name)
    (.mk ([
      ("label", s!"{name op}\\n{output.name}\n{output.type.shape}"),
    ] ++ attrs))

/- Makes a graph edge from one tensor to another. The names should be sanitized -/
def makeEdge (source : String) (dest : String) : Edge :=
  .mk
    source
    dest
    (.mk [])

/- Produces a graph from a K3 function. -/
def graph (f : FunctionK3) : Graph := Id.run do
  let mut vertices := []
  let mut edges := []
  for op in f.statements do
    let targets := targets op
    let tensorDeps := dependencies op
    let scalarDeps := scalarDependencies op |>.filterMap fun dep =>
      match dep with
      | .vector name size dtype =>
        .some { name, type := ⟨⟨[size]⟩, dtype⟩ }
      | _ => none
    let deps := tensorDeps ++ scalarDeps
    for target in targets do
      vertices := (makeOpNode op target) :: vertices
    for dep in deps do
      for target in targets do
        edges := (makeEdge (sanitize dep.name) (sanitize target.name)) :: edges

  for arg in f.inputs do
    vertices := (makeArgNode arg.name) :: vertices

  ⟨f.name, vertices, edges⟩

end KLR.K.K3
