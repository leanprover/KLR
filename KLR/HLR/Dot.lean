import SHerLOC.Analysis.Graph
import KLR.HLR.AST

abbrev Vertex := StableHLO.Analysis.Vertex
abbrev Graph := StableHLO.Analysis.Graph
abbrev Edge := StableHLO.Analysis.Edge

namespace KLR.HLR

def makeNodeName (var : String) : String :=
  s!"node_{var}"

def makeConstNodeName (var use : String) : String :=
  s!"node_const_{var}_{use}"

def makeRawNode (id label : String) : Vertex :=
  .mk
    id
    (StableHLO.Analysis.AttributeList.mk [
      ("label", label),
    ])
def makeOpNode (op : Operator) (output : String) : Vertex :=
  let attrs := match op with
  | .arg _ => [
      ("shape", "diamond"),
      ("style", "filled"),
      ("fillcolor", "lightgreen"),
      ("color", "green")
    ]
  | .batchMatmul _ _ _ => [
      ("style", "filled"),
      ("fillcolor", "lightpink"),
      ("color", "red")
    ]
  | .slice _ _ _ _ => [
      ("style", "filled"),
      ("fillcolor", "lightblue"),
      ("color", "blue")
    ]
  | _ => []
  .mk
    (makeNodeName output)
    (.mk ([
      ("label", s!"{opName op}\\n{output}"),
    ] ++ attrs))

def makeConstNode (name : String) (usedAt : String): Vertex :=
  .mk
    (makeConstNodeName name usedAt)
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

def hlrToGraph (f : HLR.Function) : Graph := Id.run do
  let mut vertices := []
  let mut edges := []
  let mut consts := f.statements.filterMap (fun s => match s with
    | .assign v (.const _ _) _ => .some v
    | _ => .none)
  let (makeEdges : List String → String → (List Vertex) × (List Edge)) := (fun inputs output =>
    inputs.map (fun input =>
      if consts.contains input then
        let vertices := (makeConstNode input output) :: []
        let edges := (makeEdge (makeConstNodeName input output) (makeNodeName output)) :: []
        (vertices, edges)
      else
        let edges := (makeEdge (makeNodeName input) (makeNodeName output)) :: []
        ([], edges)) |> List.unzip |> fun (vertices, edges) => (vertices.flatten, edges.flatten))

  for s in f.statements do
    match s with
    | .assign _ (.const _ _) _ => ()
    | .assign v op _ =>
      vertices := makeOpNode op v :: vertices
      let (newVertices, newEdges) := makeEdges (dependencies op) v
      vertices := newVertices ++ vertices
      edges := newEdges ++ edges
    | .ret v =>
      vertices := makeRawNode "return" "return" :: vertices
      edges := (makeEdge (makeNodeName v) "return") :: edges
    | .comment _ => ()

  .mk f.name vertices edges
