import KLR.TGRKLR.CompileK3
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
  | .matmul .. => [
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
    let deps := dependencies op
    let targets := targets op
    let vecTargets := scalarTargets op
    let vecDeps := scalarDependencies op

    -- add tensor vertices
    for target in targets do
      vertices := (makeOpNode op target) :: vertices
    -- add scalar vertices
    for vecTarget in vecTargets do
      match vecTarget with
      | .vector vecTargetName vecTargetSize =>
        vertices := (makeVecNode vecTargetName vecTargetSize) :: vertices
      | _ => ()

    -- add tensor-tensor edges
    for dep in deps do
      for target in targets do
        edges := (makeEdge (sanitize dep.name) (sanitize target.name)) :: edges
    -- add scalar-scalar edges
    for vecTarget in vecTargets do
      match vecTarget with
      | .vector vecTargetName _ =>
        for vecDep in vecDeps do
          match vecDep with
          | .vector vecDepName _ =>
            edges := (makeEdge (sanitize vecDepName) (sanitize vecTargetName)) :: edges
          | _ => ()
      | _ => ()
    -- add tensor-scalar edges
    for target in targets do
      for vecDep in vecDeps do
        match vecDep with
        | .vector vecDepName _ =>
          edges := (makeEdge (sanitize vecDepName) (sanitize target.name)) :: edges
        | _ => ()
    -- add scalar-tensor edges
    for vecTarget in vecTargets do
      for dep in deps do
        match vecTarget with
        | .vector vecTargetName _ =>
          edges := (makeEdge (sanitize dep.name) (sanitize vecTargetName)) :: edges
        | _ => ()

  for arg in f.inputs do
    vertices := (makeArgNode arg.name) :: vertices

  .mk f.name vertices edges

end KLR.TGRKLR.K3
