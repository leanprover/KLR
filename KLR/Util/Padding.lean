/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Util.FromBytes
import Util.NumBytes
import Util.ToBytes

namespace KLR.Util

open Lean(Json ToJson toJson)

structure Padding (n : Nat) where
deriving Inhabited

namespace Padding

instance : GetElem (Padding n) Nat Nat (fun _ i => i < n) where
  getElem _ _ _ := 0

#guard
  let v : Padding 5 := Padding.mk
  v[0] == 0 && v[4]! == 0 && v[5]?.isNone

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

instance : ToJson (Padding n) where
  toJson _ := Json.str s!"Padding of size {n}"

instance : ToSexp (Padding n) where
  toSexp _ := Sexp.atom s!"Padding of size {n}"

instance : FromSexp (Padding n) where
  fromSexp? _ := default

end Padding

end KLR.Util
