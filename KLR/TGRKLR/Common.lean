import KLR.Core

namespace KLR.TGRKLR

structure HbmLocation (Scalar : Type) where
  name : String
  offset : Scalar
  pattern : List Core.APPair
deriving Inhabited, Repr, BEq

instance [ToString T] : ToString (HbmLocation T) where
  toString
  | .mk name offset pattern => s!"HbmLoc(at: {name}[{offset}], pattern: {repr pattern})"
