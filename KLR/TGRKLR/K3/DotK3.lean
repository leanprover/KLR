import KLR.TGRKLR.K3.AST
import SHerLOC.Analysis.Graph

open StableHLO.Analysis (Graph Edge Vertex)

namespace KLR.TGRKLR.K3

def sanitize (var : String) : String :=
  s!"node_{var}"

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
      ("label", s!"{name op}\\n{output.name}\n{output.shape.shape}"),
    ] ++ attrs))
def makeVecNode (name : String) (size : Nat) : Vertex :=
  .mk
    (sanitize name)
    (.mk [
      ("label", s!"{name}\\n{size}"),
      ("shape", "box"),
      ("style", "filled"),
      ("fillcolor", "lightblue"),
      ("color", "blue")
    ])

def makeEdge (source : String) (dest : String) : Edge :=
  .mk
    source
    dest
    (.mk [])

def graph (f : FunctionK3) : Graph := Id.run do
  let mut vertices := []
  let mut edges := []
  for op in f.statements do
    let targets := (targets op)
    let deps := dependencies op ++ (scalarDependencies op |>.filterMap fun dep =>
      match dep with
      | .vector name size dtype => .some {name, shape:={shape:=⟨[size]⟩, dtype} : TensorK3}
      | _ => none)

    -- add tensor vertices
    for target in targets do
      vertices := (makeOpNode op target) :: vertices

    -- add tensor-tensor edges
    for dep in deps do
      for target in targets do
        edges := (makeEdge (sanitize dep.name) (sanitize target.name)) :: edges

  for arg in f.inputs do
    vertices := (makeArgNode arg.name) :: vertices

  .mk f.name vertices edges

end KLR.TGRKLR.K3
