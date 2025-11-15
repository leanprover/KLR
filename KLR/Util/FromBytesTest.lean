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

import KLR.Util.FromBytes

namespace KLR.Util

#guard fromBytes (Vector UInt8 4) ⟨ #[0, 1, 0, 2] ⟩ == .ok (Vector.mk #[(0 : UInt8), 1, 0, 2] (by simp), ⟨ #[] ⟩)

private structure Foo where
  x : Int8
  y : Int16
  z : Int32
deriving BEq, FromBytes, Inhabited, NumBytes

#guard fromBytes Foo ⟨ #[0, 1, 0, 2, 0, 0, 0, 77] ⟩ == .ok (Foo.mk 0x0 0x1 0x2, ⟨ #[77] ⟩)

private structure Bar where
  y : Foo
  z : Int32
deriving BEq, FromBytes, Inhabited, NumBytes

#guard fromBytes Bar ⟨ #[0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 77] ⟩ == .ok (Bar.mk (Foo.mk 0x0 0x1 0x2) 3, ⟨ #[77] ⟩)

/--
error: deriving FromBytes only works on single structures
-/
#guard_msgs in
mutual
private structure Foo1 where
  x : Int8
deriving FromBytes

private structure Foo2 where
  x : Int8
deriving NumBytes
end

/--
error: deriving FromBytes only works on single structures
-/
#guard_msgs in
mutual
private structure Bar1 where
  x : Int8
deriving FromBytes

private structure Bar2 where
  x : Int8
-- No deriving clause here
end

/--
error: deriving FromBytes only works on single structures
-/
#guard_msgs in
private inductive Baz where
| x : Int -> Baz
| y : Nat -> Baz
deriving FromBytes
