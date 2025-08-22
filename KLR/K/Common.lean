import KLR.Core

namespace KLR.K

/- A region of HBM, described as an offset from some named tensor as well as
an access pattern. The access pattern is in source-order (slowest-first), not
ISA-order (fastest-first) -/
structure HbmLocation (Scalar : Type) where
  name : String
  offset : Scalar
  pattern : List Core.APPair
deriving Inhabited, Repr, BEq

instance [ToString T] : ToString (HbmLocation T) where
  toString
  | .mk name offset pattern => s!"HbmLoc(at: {name}[{offset}], pattern: {repr pattern})"
