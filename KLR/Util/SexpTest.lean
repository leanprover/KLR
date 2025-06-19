/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import Util.Sexp

namespace KLR.Util.Sexp

#guard fromSexp UInt8 (atom "5") == .ok 5
#guard fromSexp UInt8 (atom "5.5") == .error "Can't parse 5.5 as an Int"
#guard toSexp (5 : UInt8) == atom "5"

private structure Foo where
  x : Nat
  y : UInt8
deriving ToSexp

#guard toSexp (Foo.mk 5 19) == list [atom "5", atom "19"]

private inductive Bar where
| x (n : Nat) (k : Nat)
| y (m : Foo)
deriving ToSexp

#guard toSexp (Bar.x 5 7) == list [atom "x", atom "5", atom "7"]
#guard toSexp (Bar.y (Foo.mk 5 10)) == list [atom "y", list [atom "5", atom "10"]]
