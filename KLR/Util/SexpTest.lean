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
#guard @fromSexp? Foo _ (sexp% ((x 5) (z 9))) == .error "No field named z in Foo"

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

#guard (@fromSexp? A1 _ (sexp% (x (n 5) (zzz 9)))) == .error "No field named zzz in A1.x"

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

-- Show structs with all defaults can be emitted entirely when in another structure or inductive
private structure Default4 where
  x : Nat := 8
  y : Nat := 7
deriving BEq, FromSexp, Repr

private inductive Default5 where
| Foo (x : Default4 := {})
deriving BEq, FromSexp, Repr

#guard @fromSexp? Default5 _ (sexp%(Foo)) == .ok (Default5.Foo {})

private structure Default6 where
deriving BEq, FromSexp, Repr

#guard @fromSexp? Default6 _ (sexp%()) == .ok (Default6.mk)

structure pseudo_core_barrier where
  id : UInt32
  semaphore : UInt32
deriving FromSexp

-- Was broken in earlier version. It generated
--    assocWithDefault✝ _ sexp✝ "arg" (id { })
-- but id was not the identity function, but the projection
private structure IdArg where
deriving FromSexp

private structure Id where
  id : Nat
  arg : IdArg := {}
deriving FromSexp
