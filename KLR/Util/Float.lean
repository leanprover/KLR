/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
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

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (f : Float) : roundTrip f := by plausible
