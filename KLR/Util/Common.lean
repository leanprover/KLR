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

namespace KLR

/-
The default choice for an error monad is `Except String`, used for simple
computations that can fail.

Provide automatic lifting of Err to any monad that supports throwing strings
as errors.
-/
abbrev Err := Except String

instance : MonadLift Err IO where
  monadLift
  | .ok x => return x
  | .error s => throw $ .userError s

instance [Monad m] [MonadExcept String m] : MonadLift Err m where
  monadLift
    | .ok x => return x
    | .error s => throw s

instance [BEq a] : BEq (Err a) where
  beq x y := match x, y with
  | .ok a, .ok b => a == b
  | .error msg, .error msg' => msg == msg'
  | _, _ => false

/-
The default choice for a state monad is `EStateM String`.
-/
abbrev StM := EStateM String

def impossible {a : Type} [h : Inhabited a] (msg : String := "") :=
  @panic a h s!"Invariant violation: {msg}"

def _root_.Except.get! [Inhabited α] (v : Except ε α) : α :=
  match v with
  | .error _ => impossible
  | .ok x => x

def _root_.Except.getD (v : Except ε α) (default : α) : α :=
  match v with
  | .ok v => v
  | .error _ => default

-- TODO: Deprecate this
def get! [Inhabited a] (x : Err a) : a :=
  x.get!

def natDivCeil (num denom : Nat) : Nat := (num + denom - 1) / denom

end KLR
