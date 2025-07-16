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

import Lean.Elab
import Util.Common

open KLR(Err)
open Lean(MonadError Name Syntax Term)
open Lean.Elab.Term(TermElabM elabBinders elabTerm)

/-
This namespace is intended to be a library of utilities for
metaprogramming in KLR. The functions we've been using are spread
over many files and namespaces, and are hard to remember. Let's use
this to organize as many of our standard patterns as possible. Some
of them, like stringToStrLit are just abbreviations for other library
functions. Even so, I still think there's value to having them in one spot.
-/
namespace KLR.Util.Meta

def stringToStrLit (s : String) : Term := Syntax.mkStrLit s

def nameToIdent (n : Name) : Term := Lean.mkIdent n

def nameToString [Monad m] [MonadError m] (n : Name) : m String := do
  let .str _ s := n | throwError "Not a string name"
  return s

def nameToStrLit [Monad m] [MonadError m] (n : Name) : m Term := do
  return stringToStrLit (<- nameToString n)

end KLR.Util.Meta
