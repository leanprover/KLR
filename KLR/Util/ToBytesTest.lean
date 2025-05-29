import Util.ToBytes

namespace KLR.Util

private structure Foo where
  x : Int8
  y : Int16
  z : Int32
deriving ToBytes

#guard toBytes (Foo.mk 0x0 0x1 0x2) == ⟨ #[0, 1, 0, 2, 0, 0, 0] ⟩

private structure Bar where
  y : Foo
  z : Int32
deriving ToBytes

#guard toBytes (Bar.mk (Foo.mk 0x0 0x1 0x2) 3) == ⟨ #[0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0] ⟩

/--
error: deriving ToBytes only works on single structures
-/
#guard_msgs in
mutual
private structure Foo1 where
  x : Int8
deriving ToBytes

private structure Foo2 where
  x : Int8
deriving NumBytes
end

/--
error: deriving ToBytes only works on single structures
-/
#guard_msgs in
mutual
private structure Bar1 where
  x : Int8
deriving ToBytes

private structure Bar2 where
  x : Int8
-- No deriving clause here
end

/--
error: deriving ToBytes only works on single structures
-/
#guard_msgs in
private inductive Baz where
| x : Int -> Baz
| y : Nat -> Baz
deriving ToBytes
