import Lean
open Lean.Meta

initialize
  discard <| registerSimpAttr `df_simp "Dataflow definitions to be fed to simp"

initialize
  discard <| registerSimpAttr `nm_simp "Nodemap definitions to be fed to simp"
