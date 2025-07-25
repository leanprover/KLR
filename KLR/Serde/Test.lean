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

import KLR.Serde.Attr
import KLR.Serde.Elab

/-
Tests for the serde attribute.

New attributes must be defined in a separate module from where they are used.
This module has some basic compile-time tests and documentation for the Attr
module.
-/

namespace KLR.Serde.Test

/-
The serde attribute allows you to associate a natural number with a type or
value constructor. The main motivation for this is to support serialization and
de-serialization.

For example, we can assign a tag to the inductive type `Foo`.
-/

@[serde tag = 3]
inductive Foo where
  | a : Int -> Foo
  | b : Float -> Foo

/-
Then, from a meta-program we can query this value
-/

/-- info: some 3 -/
#guard_msgs in #eval serdeTag ``Foo

/-
You can also assign tags to value constructors, and query these values from
meta-programs. Any value constructors without assigned tags will return `none`
if queried.
-/

attribute [serde tag = 4] Foo.a

/-- info: some 4 -/
#guard_msgs in #eval serdeTag ``Foo.a

/-- info: none -/
#guard_msgs in #eval serdeTag ``Foo.b

/-
The `serdeMap` function will return a mapping of all the values constructors
for a type and their associated tags. This function will automatically assign
tags to any constructors that do not have one assigned. This works similar to C
enums: if a constructor doesn't have a tag, it is assigned to be the previous
constructor's tag plus one. Numbering starts at zero.
-/

/-- info: [(`KLR.Serde.Test.Foo.a, 4), (`KLR.Serde.Test.Foo.b, 5)] -/
#guard_msgs in#eval serdeMap ``Foo

/-
The serde tags can be assigned (or reassigned) away from the type definition.
-/

attribute [serde tag = 11] Foo
attribute [serde tag = 7] Foo.a
attribute [serde tag = 3] Foo.b

/-- info: some 11 -/
#guard_msgs in #eval serdeTag ``Foo

/-- info: some 7 -/
#guard_msgs in #eval serdeTag ``Foo.a

/-- info: some 3 -/
#guard_msgs in #eval serdeTag ``Foo.b

/-
For convenience, the `serdeTags` function returns all of the data for a given type.
-/

/-- info: (11, [(`KLR.Serde.Test.Foo.a, 7), (`KLR.Serde.Test.Foo.b, 3)]) -/
#guard_msgs in #eval serdeTags ``Foo

/-
All of these things can also be used on structures, although the map of value
constructors is less useful.
-/

@[serde tag = 1]
structure Bar where
  x : Int
  y : Int

/-- info: (1, [(`KLR.Serde.Test.Bar.mk, 0)]) -/
#guard_msgs in #eval serdeTags ``Bar


/-
While not the main motivation, `serdeMap` can be used on any lean type to get
the Lean constructor numbers: the numbering used by `serdeMap` is compatible
with how Lean numbers constructors internally. This may be useful for C code
that needs to work with Lean values. Foe example, we can calculate what the
first argument of `lean_alloc_ctor` should be for the `Lean.Name` type.
-/

/-- info:
#define Lean_Name_anonymous 0
#define Lean_Name_str 1
#define Lean_Name_num 2
-/
#guard_msgs in #eval do
  for (n,v) in <- serdeMap ``Lean.Name do
    let n := n.toString.replace "." "_"
    IO.println s!"#define {n} {v}"

/-
Deriving tests
-/

@[serde tag=7]
inductive Z where
  | a : Nat -> Z
  | b : Bool -> Z
  deriving BEq, Repr, ToCBOR, FromCBOR

#guard (toCBOR (Z.a 0)).data == #[0xd9, 7, 0, 0x81, 0]
#guard (toCBOR (Z.b true)).data == #[0xd9, 7, 1, 0x81, 0xf5]

#guard roundtrip (Z.a 280)
#guard roundtrip (Z.b false)

mutual
@[serde tag=1]
structure X (a : Type u) where
  i : a
  b : Bool
  deriving BEq, Repr, ToCBOR, FromCBOR

@[serde tag=2]
inductive Y (a : Type u) where
  | n : Nat -> Y a
  | x : X a -> Y a
  deriving BEq, Repr, ToCBOR, FromCBOR
end

#guard (toCBOR (X.mk true false)).data == #[0xd9, 1, 0, 0x82, 0xf5, 0xf4]
#guard (toCBOR (Y.n 7 : Y Bool)).data == #[0xd9, 2, 0, 0x81, 7]
#guard (toCBOR (Y.x (X.mk true false))).data ==
  #[0xd9, 2, 1, 0x81, 0xd9, 1, 0, 0x82, 0xf5, 0xf4]

#guard roundtrip (X.mk true false)
#guard roundtrip (Y.n 7 : Y Bool)
#guard roundtrip (Y.x (X.mk true false))
