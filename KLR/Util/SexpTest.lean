/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import Util.Sexp
import TensorLib

open Std(HashMap)
open TensorLib(Err)

open Std(HashMap)

namespace KLR.Util.Sexp

#guard @fromSexp? UInt8 _ (atom "5") == .ok 5
#guard @fromSexp? UInt8 _ (atom "5.5") == .error "Can't parse 5.5 as an Int"
#guard toSexp (5 : UInt8) == atom "5"

instance : BEq (Std.HashMap Nat Nat) where
  beq x y := x.toList == y.toList

#guard toSexp (HashMap.ofList [(1, 2)]) == sexp%((1 2))
#guard fromSexp? (sexp%((1 2))) == .ok (HashMap.ofList [(1, 2)])

private def roundTrip [BEq a] [ToSexp a] [FromSexp a] (x : a) : Bool :=
  let y := toSexp x
  match fromSexp? y with
  | .error _ => false
  | .ok z => x == z


#guard roundTrip (HashMap.ofList [(1, 2), (3, 4)])

#guard roundTrip true
#guard roundTrip false

#guard roundTrip 1.3
#guard roundTrip (1.0 / 0.0)
#guard roundTrip (-1.0 / 0.0)
#guard toSexp (0.0 / 0.0) == atom "NaN"
#guard
  match @fromSexp? Float _ (atom "NaN") with
  | .ok f => f.isNaN
  | _ => false

private structure Foo where
  x : Nat
  y : Nat
deriving BEq, FromSexp, Repr, ToSexp

#guard toSexp (Foo.mk 5 19) == sexp% ((x 5) (y 19))
#guard roundTrip (Foo.mk 5 19)
-- non-named field syntax
#guard fromSexp? (sexp% (5 7)) == .ok (Foo.mk 5 7)
#guard !(@fromSexp? Foo _ (sexp% (5 7 8))).isOk

-- named field syntax
#guard fromSexp? (sexp% ((x 5) (y 7))) == .ok (Foo.mk 5 7)

private inductive E where
| a
| b
deriving BEq, FromSexp, Repr, ToSexp

#guard toSexp E.a == sexp% a
#guard fromSexp? (sexp% a) == .ok E.a
#guard roundTrip E.a

private inductive A1 where
| x (n : Nat) (m : Nat := 7)
| y : Nat -> A1
| z (n : Nat) : Nat -> A1
deriving BEq, FromSexp, ToSexp, Repr, Lean.ToJson, Lean.FromJson

#guard toSexp (A1.x 5 7) == sexp% (x (n 5) (m 7))
#guard toSexp (A1.y 5) == sexp% (y 5)
#guard fromSexp? (sexp% (y 5)) == .ok (A1.y 5)
#guard toSexp (A1.z 5 6) == sexp% (z 5 6)
#guard roundTrip (A1.x 5)
#guard roundTrip (A1.y 5)
#guard roundTrip (A1.z 5 6)
#guard fromSexp? (sexp% (x (n 5))) == .ok (A1.x 5)

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
#guard fromSexp? (sexp% (x (n 5) (k 7))) == .ok (Bar.x 5 7)
-- unnamed syntax
#guard fromSexp? (sexp% (x (n 5) (k 7))) == .ok (Bar.x 5 7)
#guard fromSexp? (sexp% (x 5 7)) == .ok (Bar.x 5 7)
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

private structure Default1 where
  x : Nat
  y : Nat := 7
deriving BEq, FromSexp

#guard (@fromSexp? Default1 _ (sexp%((x 5)))) == .ok { x := 5, y := 7 }
#guard (@fromSexp? Default1 _ (sexp%((x 5) (y 8)))) == .ok { x := 5, y := 8 }
#guard !(@fromSexp? Default1 _ (sexp%((y 8)))).isOk

private structure Default2 where
  y : Nat := 7
  z : Nat := 5
  w : Nat := 10
  x : Nat
deriving BEq, FromSexp

#guard (@fromSexp? Default2 _ (sexp%((x 5)))) == .ok { x := 5, y := 7, z := 5, w := 10 }
#guard (@fromSexp? Default2 _ (sexp%((x 5) (w 8)))) == .ok { x := 5, y := 7, z := 5, w := 8 }
#guard !(@fromSexp? Default2 _ (sexp%((y 8)))).isOk

private inductive Default3 where
| case1 (x : Nat) (y : Nat := 7)
| case2 (x : Nat := 7) (y : Nat)
deriving BEq, FromSexp, ToSexp

#guard toSexp (Default3.case1 (x := 5) (y := 7)) == sexp%(case1 (x 5) (y 7))
#guard @fromSexp? Default3 _ (sexp%(case2 (y 7))) == .ok (Default3.case2 7 7)
#guard !(@fromSexp? Default3 _ (sexp%(case2 (x 2)))).isOk

-- Parser tests

#guard Sexp.fromString "3.14" == .ok (.atom "3.14")
#guard Sexp.fromString "(a ok)" == .ok (sexp%(a ok))
#guard Sexp.fromString "(a (b c d) e)" == .ok (sexp%(a (b c d) e))
#guard (Sexp.fromString "(a ok) oops").isOk == false
#guard (Sexp.fromString "(a ok))").isOk == false
#guard (Sexp.fromString "(a ok").isOk == false
