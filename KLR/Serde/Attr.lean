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

import Lean

/-
# Attribute for serialization and de-serialization

This modules defines a new attribute and some meta-programming utilities for
accessing the attribute data. Note: new attributes must be defined in a
separate module from where they are used. See `Test.lean` for more details.
-/
namespace KLR.Serde
open Lean Meta

private structure SerdeTag where
  tag : Nat
  deriving Inhabited, BEq, Repr

syntax (name := serde) "serde" "tag" "=" num : attr

private initialize tags : ParametricAttribute SerdeTag <-
  registerParametricAttribute {
    name := `serde
    descr := "Assign Serde tag"
    getParam name stx := do
      let `(attr| serde tag = $t:num  ) := stx
        | throwError "invalid [serde] attribute"
      return ⟨ TSyntax.getNat t ⟩
  }

-- Return the serde tag for a name (if any)
def serdeTag [Monad m] [MonadEnv m] (name : Name) : m (Option Nat) := do
  return (tags.getParam? (<- getEnv) name).map (·.tag)

-- Check for duplicates and reverse list (private function used below)
private def checkDups (l : List (a × Nat)) : MetaM (List (a × Nat)) := do
  let rec loop l1 l2 :=
    match l1, l2 with
    | l1, [] => return l1
    | l1, x :: xs =>
      if l1.any fun p => p.2 == x.2
      then throwError s!"duplicate Serde tag found {x.2}"
      else loop (x :: l1) xs
  loop [] l

/-
Return a mapping of constructor names to serde tags for a given type. Any
constructors without assigned tags will be automatically assigned a tag
starting equal to the previous tag plus one, while avoiding any user defined
values.

One important use case is adding a new constructor. If we add a new constructor
to a type, but we don't want to add it at the end, then we can manually assign
it a tag and the other constructors will end up with their previous assignments.

inductive A | a | c | d
-- mapping is a=0, c=1, d=2

-- changed to:
inductive A | a | b | c | d
-- mapping is: a=0, b=1, c=2, d=3  (INCORRECT)

@[serde tag = 3 ] A.b
-- mapping is: a=0, b=3, c=1, d=2  (correct)

See Test.lean for more details.
-/
partial def nextTag (user : List (Option Nat)) (n : Nat) : Nat :=
  let n := n + 1
  if user.contains (some n)
  then nextTag user n
  else n

def serdeMap (name : Name) : MetaM (List (Name × Nat)) := do
  let tcs <- getConstInfoInduct name
  let user <- tcs.ctors.mapM serdeTag
  let nextTag := nextTag user
  let mut current := 0
  let mut res := []
  for ctor in tcs.ctors do
    match <- serdeTag ctor with
    | none =>
        res := (ctor, current) :: res
        current := nextTag current
    | some n =>
        res := (ctor, n) :: res
        current := nextTag n
  checkDups res

abbrev Tags := Nat × List (Name × Nat)

-- Convenience function: serdeTag and serdeMap
def serdeTags (name : Name) : MetaM Tags := do
  match <- serdeTag name with
  | none => throwError s!"No serde tags for {name}"
  | some t => return (t, <- serdeMap name)
