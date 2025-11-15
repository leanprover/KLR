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

import KLR.Util.NumBytes

open KLR.Util(NumBytes)

section Test

private structure Foo where
  x : Int8
  y : Int32
  z : Int8 × Int16
deriving Inhabited, NumBytes

#guard NumBytes.numBytes (default:Foo) == 8

/--
error: deriving NumBytes only works on single structures
-/
#guard_msgs in
mutual
private structure Foo1 where
  x : Int8
deriving NumBytes

private structure Foo2 where
  x : Int8
deriving NumBytes
end

/--
error: deriving NumBytes only works on single structures
-/
#guard_msgs in
mutual
private structure Bar1 where
  x : Int8
deriving NumBytes

private structure Bar2 where
  x : Int8
-- No deriving clause here
end

/--
error: deriving NumBytes only works on single structures
-/
#guard_msgs in
private inductive Baz where
| x : Int -> Baz
| y : Nat -> Baz
deriving NumBytes

end Test
