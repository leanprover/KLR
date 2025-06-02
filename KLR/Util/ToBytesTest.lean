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
error: deriving ToBytes only works on single structures or inductives all of whose branches have a single ToBytes argument
-/
#guard_msgs in
mutual
private structure Foo1 where
  x : Int8
deriving ToBytes

private structure Foo2 where
  x : Int8
deriving ToBytes
end

/--
error: deriving ToBytes only works on single structures or inductives all of whose branches have a single ToBytes argument
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

private inductive FooI where
| X (x : Int8)
| Y (y : Int16)
| Z (z : Int32)
deriving ToBytes

#guard toBytes (FooI.X 0x2) == ⟨ #[2] ⟩
#guard toBytes (FooI.Y 0x2) == ⟨ #[2, 0] ⟩
#guard toBytes (FooI.Z 0x2) == ⟨ #[2, 0, 0, 0] ⟩
