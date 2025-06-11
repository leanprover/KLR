import Util.FromBytes
import Util.NumBytes
import Util.ToBytes

namespace KLR.Util

structure Padding (n : Nat) where

deriving Inhabited

namespace Padding

instance : Repr (Padding n) where
  reprPrec _ _ := s!"Padding of size {n}"

instance : BEq (Padding n) where
  beq _ _ := true

instance : NumBytes (Padding n) where
  numBytes _ := n

instance : ToBytes (Padding n) where
  toBytes _ := ByteArray.zeros n

instance : FromBytes (Padding n) where
  fromBytesUnchecked arr := do
    let zeros := arr.take n
    let mut i := 0
    for byte in zeros.data do
      if byte != 0 then throw s!"Nonzero padding at index {i}"
      i := i + 1
    return (⟨⟩, arr.drop n)

end Padding

end KLR.Util
