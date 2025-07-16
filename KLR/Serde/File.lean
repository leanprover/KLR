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

import KLR.Util
import KLR.Serde.Attr
import KLR.Serde.Basic
import KLR.Serde.Elab

namespace KLR.Serde

/-
We would like all of our CBOR encoded files to be easily identifiable as KLR
files, both for our tools and for third-party tools that understand CBOR. The
CBOR specification defines a special tag value (55799), which indicates that
what follows is a CBOR encoded value. This special value is meant to help
decoders identify CBOR data streams. When this value is encoded as a CBOR
tagged value, it will be three bytes, the 16-bit tag indicator (0xd9), followed
by the big-endian representation of 55799 (0xd9 0xf7):

  0xd9 0xd9 0xf7 ,

and this three byte sequence can be used to identify a CBOR file. Quoting the
specification:

  The serialization of this tag's head is 0xd9d9f7, which does not appear to be
  in use as a distinguishing mark for any frequently used file types. In
  particular, 0xd9d9f7 is not a valid start of a Unicode text in any Unicode
  encoding if it is followed by a valid CBOR data item.

We leverage this by specifically marking our `KLRFile` structure with a tag of
0xd9, and changing the `mk` constructor to have tag 0xf7. When this is
converted to a 16-bit tag by our `cborTag` function (see Serde.Basic), we end
up with 0xd9d9f7, the "self-described CBOR" marker.

The `KLRFile` structure contains a semantic version number, and nothing else so
that tools unaware of our format can read the header. Hence, every KLR file
starts with:

  0xd9 0xd9 0xf7 0x83 major minor patch
  |    |    |    |
  |    |    |    +-- list of length 3
  |    +----+-- 55799 tag value (self-described CBOR)
  +-- CBOR code for 16-bit tagged value

This is all handled automatically by our derived instances.
-/

@[serde tag = 0xd9]
structure KLRFile where
  major : Nat := 0  -- TODO come up with a way to manage versions
  minor : Nat := 0
  patch : Nat := 12
  deriving BEq, Repr

attribute [serde tag = 0xf7] KLRFile.mk

deriving instance ToCBOR for KLRFile
deriving instance FromCBOR for KLRFile

#guard (toCBOR { : KLRFile}).take 4 == .mk #[0xd9, 0xd9, 0xf7, 0x83]
#guard (fromCBOR (toCBOR { : KLRFile }) : Err KLRFile) == .ok { : KLRFile }

/-
Immediately following the KLRFile structure we place a KLRMetaData structure.
We are careful to choose a tag value (0xeb00) that is unassigned according to:

  https://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml

Because everything is contained within this tagged value, we do not have to
worry about avoiding assigned tags on our other (internal) types.
-/

-- TODO what do we need here?
@[serde tag = 0xeb]
structure KLRMetaData where
  format : String := "NKI"
  deriving BEq, Repr, ToCBOR, FromCBOR
