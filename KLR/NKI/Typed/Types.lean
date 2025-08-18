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

import KLR.NKI.Typed.Basic
import KLR.NKI.Typed.Context
import KLR.Py

namespace KLR.NKI.Typed

open KLR.Py (Span Ident FileInfo)

structure State where
  span       : Option Span := none
  nameCount  : Nat         := 0
  warnings   : List String := []
  retTyp     : Option Typ  := none
  inLoop     : Bool        := false

abbrev ElabM := ReaderT FileInfo <| EStateM String State

/-! # -----------Start: Error Reporting-------------- -/

def throwAt {α} (span : Span) (pre : String) (msg : String) : ElabM α := do
  let msg := (← read).formatError pre msg span
  MonadExcept.throw msg

def throw {α} (pre : String) (msg : String) : ElabM α := do
  let pos := (← get).span.getD {}
  throwAt pos pre msg

def throwInternal {α} (msg : String) : ElabM α :=
  throw "InternalError" msg

def throwSyntax {α} (msg : String) : ElabM α :=
  throw "SyntaxError" msg

def throwType {α} (msg : String) : ElabM α :=
  throw "TypeError" msg

def throwEmptyStmts {α} : ElabM α :=
  throwType "cannot have empty statements here"

def throwUnsupported {α} (msg : String) : ElabM α :=
  throw "Unsupported" msg

/-! # -----------End: Error Reporting-------------- -/

/-! # -----------Start: Getters/Setters-------------- -/

def getSpan! : ElabM Span := do
  let some span := (← get).span
    | throwInternal "missing position information"
  return span

def getRetTyp : ElabM (Option Typ) :=
  return (← get).retTyp

def inLoop : ElabM Bool :=
  return (← get).inLoop

def enterLoop : ElabM Unit :=
  modifyGet fun s =>
  ((), {s with inLoop := true})

def withLoop {α} (x : ElabM α) : ElabM α := do
  let saved ← inLoop
  enterLoop
  let a ← x
  modifyGet fun s =>
  (a, {s with inLoop := saved})

def withRetTyp {α} (retTyp : Typ) (x : ElabM α) : ElabM α := do
  let s ← get
  let saved := s.retTyp
  set {s with retTyp := retTyp}
  let a ← x
  modifyGet fun s =>
  (a, {s with retTyp := saved})

def withSpan {α} (span : Span) (x : ElabM α) : ElabM α := do
  let s ← get
  let savedSpan := s.span
  set {s with span := span}
  let a ← x
  modifyGet fun s =>
  (a, {s with span := savedSpan})

def applyCtxToRet (Γ : Context) : ElabM Unit :=
  modifyGet fun s =>
  ((), {s with retTyp := s.retTyp.map Γ.apply})

/-! # -----------End: Getters/Setters-------------- -/

/-! # -----------Start: Name Generation-------------- -/

def freshName : ElabM Ident :=
  modifyGet fun s =>
  (s!"\'T{s.nameCount}", {s with nameCount := s.nameCount + 1})

/-! # -----------End: Name Generation-------------- -/
