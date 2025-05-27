/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Util.NumBytes

open KLR.Util(NumBytes)

section Test

private structure Foo where
  x : Int8
  y : Int32
  z : Int8 × Int16
deriving Inhabited, NumBytes

#guard NumBytes.numBytes (default:Foo) == 8

/--
error: deriving NumBytes does not work on mutually inductive types
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
error: deriving NumBytes does not work on mutually inductive types
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

end Test
