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

private def roundTrip [BEq a] [ToSexp a] [FromSexp a] (x : a) : Bool :=
  let y := toSexp x
  match fromSexp a y with
  | .error _ => false
  | .ok z => x == z

private structure Foo where
  x : Nat
  y : Nat
deriving BEq, FromSexp, Repr, ToSexp

#guard toSexp (Foo.mk 5 19) == sexp% ((x 5) (y 19))
#guard roundTrip (Foo.mk 5 19)
-- non-named field syntax
#guard fromSexp Foo (sexp% (5 7)) == .ok (Foo.mk 5 7)
#guard !(fromSexp Foo (sexp% (5 7 8))).isOk

-- named field syntax
#guard fromSexp Foo (sexp% ((x 5) (y 7))) == .ok (Foo.mk 5 7)

private inductive E where
| a
| b
deriving BEq, FromSexp, Repr, ToSexp

#guard toSexp E.a == sexp% a
#guard fromSexp E (sexp% a) == .ok E.a
#guard roundTrip E.a

private inductive A1 where
| x (n : Nat)
| y : Nat -> A1
| z (n : Nat) : Nat -> A1
deriving BEq, FromSexp, ToSexp, Repr, Lean.ToJson, Lean.FromJson

#guard toSexp (A1.x 5) == sexp% (x (n 5))
#guard toSexp (A1.y 5) == sexp% (y 5)
#guard fromSexp A1 (sexp% (y 5)) == .ok (A1.y 5)
#guard toSexp (A1.z 5 6) == sexp% (z 5 6)
#guard roundTrip (A1.x 5)
#guard roundTrip (A1.y 5)
#guard roundTrip (A1.z 5 6)
#guard fromSexp A1 (sexp% (x (n 5))) == .ok (A1.x 5)

private inductive A2 where
| x : Nat -> A2
| y (n : Nat)
deriving BEq, FromSexp, Repr, ToSexp, Lean.FromJson, Lean.ToJson

#guard toSexp (A2.x 5) == sexp% (x 5)
#guard roundTrip (A2.x 5)
#guard roundTrip (A2.y 5)

private inductive Bar where
| x (n : Nat) (k : Nat)
| y (m : Foo)
deriving BEq, FromSexp, Repr, ToSexp

#guard toSexp (Bar.x 5 7) == sexp% (x (n 5) (k 7))
#guard toSexp (Bar.y (Foo.mk 5 10)) == sexp% (y (m ((x 5) (y 10))))
#guard fromSexp Bar (sexp% (x (n 5) (k 7))) == .ok (Bar.x 5 7)
-- unnamed syntax
#guard fromSexp Bar (sexp% (x 5 7)) == .ok (Bar.x 5 7)
#guard roundTrip (Bar.x 5 7)
#guard roundTrip (Bar.y (Foo.mk 5 19))

mutual
private structure A where
  x : Nat
  y : Option B
deriving BEq, FromSexp, ToSexp

private structure B where
  z : A
deriving BEq, FromSexp, ToSexp
end

#guard
  let ex := A.mk 5 (some (B.mk (A.mk 7 none)))
  toSexp ex == sexp%((x 5) (y (((z ((x 7) (y ())))))))

#guard roundTrip $ B.mk (A.mk 7 (some (B.mk (A.mk 8 none))))
