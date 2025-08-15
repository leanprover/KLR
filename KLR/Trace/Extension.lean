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
Definition of an enviromnet extension for tracking compiler builtins.
Environment extensions have to be declared in separate modules from where they are used.

See also:
  Builtin.lean - population of the environment in the `nki` macro.
  Term.lean - use of the environment to construct builtin list.
-/

namespace KLR.Trace
open Lean

structure Builtin where
  nkiName : Name
  leanName : Name
  deriving Repr

structure Builtins where
  builtins : Array Builtin := #[]
  deriving Inhabited, Repr

def addEntry (s : Builtins) (e : Builtin) :=
  { s with builtins := s.builtins.push e }

initialize extension : SimplePersistentEnvExtension Builtin Builtins <-
  registerSimplePersistentEnvExtension {
    addEntryFn := addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries addEntry {} es)
  }
