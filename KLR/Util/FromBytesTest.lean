import Util.FromBytes

namespace KLR.Util

private structure Foo where
  x : Int8
  y : Int16
  z : Int32
deriving BEq, FromBytes, Inhabited, NumBytes

#guard fromBytes ⟨ #[0, 1, 0, 2, 0, 0, 0, 77] ⟩ == .ok (Foo.mk 0x0 0x1 0x2, ⟨ #[77] ⟩)

private structure Bar where
  y : Foo
  z : Int32
deriving BEq, FromBytes, Inhabited, NumBytes

#guard fromBytes ⟨ #[0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 77] ⟩ == .ok (Bar.mk (Foo.mk 0x0 0x1 0x2) 3, ⟨ #[77] ⟩)

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
