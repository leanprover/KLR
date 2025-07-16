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

import Util.Common
import Util.Plausible

/-
Utilities for the builtin Float types
-/

namespace KLR.Util

/-
A simple implementation of String -> Float

Note: Could easily add support for e.g. 3e5 since ofScientific supports this.
-/

private def sign : List Char -> (Bool × List Char)
  | '+' :: s => (true, s)
  | '-' :: s => (false, s)
  | s => (true, s)

private def dot : List Char -> (Bool × List Char)
  | '.' :: s => (true, s)
  | s => (false, s)

-- Note: String.toNat? would require we find the dot and split the string,
-- so just do the whole thing here in one spot
private def nat (acc : Nat) : List Char -> (Nat × List Char)
  | [] => (acc, [])
  | ch :: s => Id.run do
      if ch < '0' || ch > '9' then
        return (acc, ch :: s)
      let n := ch.val - '0'.val
      let acc := acc * 10 + n.toNat
      nat acc s

private def floatParts (cs : List Char) : (Bool × Nat × Nat) :=
  let (sgn, cs) := sign cs
  let (a, cs) := nat 0 cs
  let (haveDot, cs) := dot cs
  if haveDot then
    let (b, cs') := nat 0 cs
    let d := cs.length - cs'.length
    let m := a * 10^d + b
    (sgn, m, d)
  else
    (sgn, a, 0)

def parseFloat (s : String) : Float :=
  match s with
  | "NaN" => 0.0 / 0.0
  | "inf" => 1.0 / 0.0
  | "-inf" => -1.0 / 0.0
  | _ =>
    let (sgn, m, d) := floatParts s.toList
    let f := Float.ofScientific m true d
    if sgn then f else -f

-- I tried to extract the logic between parseFloat and parseFloat32 but
-- the general form is more painful than the copying of 5 lines of code.
def parseFloat32 (s : String) : Float32 :=
  match s with
  | "NaN" => 0.0 / 0.0
  | "inf" => 1.0 / 0.0
  | "-inf" => -1.0 / 0.0
  | _ =>
    let (sgn, m, d) := floatParts s.toList
    let f := Float32.ofScientific m true d
    if sgn then f else -f

private def roundTrip (f : Float) : Bool :=
  let f' := parseFloat f.toString
  if f.isNaN then f'.isNaN
  else if f.isInf then f == f'
  else (f - f').abs < 0.000001

#guard roundTrip (0.0 / 0.0)
#guard roundTrip (1.0 / 0.0)
#guard roundTrip (-1.0 / 0.0)
#guard roundTrip 0.0
#guard roundTrip (-0.0)
#guard roundTrip (-34.55)
#guard roundTrip 3.1415926

private def roundTrip32 (f : Float32) : Bool :=
  let f' := parseFloat32 f.toString
  if f.isNaN then f'.isNaN
  else if f.isInf then f == f'
  else (f - f').abs < 0.000001

#guard roundTrip32 (0.0 / 0.0)
#guard roundTrip32 (1.0 / 0.0)
#guard roundTrip32 (-1.0 / 0.0)
#guard roundTrip32 0.0
#guard roundTrip32 (-0.0)
#guard roundTrip32 (-34.55)
#guard roundTrip32 3.1415926

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (f : Float) : roundTrip f := by plausible
