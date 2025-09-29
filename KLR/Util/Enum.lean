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
import TensorLib.Common
import Util.Hex
import Util.Sexp

open KLR.Util.Hex(encode)
open KLR.Util(FromSexp ToSexp)
open Lean(FromJson Json Macro MacroM Syntax TSyntax TSyntaxArray ToJson mkIdent fromJson? toJson)
open Lean.Parser.Command(declModifiers)
open Lean.Parser.Term(matchAltExpr)
open TensorLib(get!)

namespace KLR.Util

class Enum (a : Type) where
  toUInt8 : a -> UInt8
  fromUInt8 : UInt8 -> Except String a

private def hasDuplicate [BEq a] (xs : List a) : Option a := Id.run do
  let mut ys := []
  for x in xs do
    if ys.contains x then return (some x)
    ys := x :: ys
  return none

private def u8ToHex (x : UInt8) : String := "0x" ++ (encode ⟨ #[x] ⟩).toUpper

#guard u8ToHex 0xff == "0xFF"

private partial def nextNat (nats : Array Nat) (current : Nat) : Array Nat × Nat :=
  if nats.contains current
  then nextNat nats (current + 1)
  else (nats.push current, current)

open Lean.Parser.Command
open Lean.Parser.Term

syntax item := Lean.Parser.Command.ctor (":=" num)?
syntax items := manyIndent(item)
syntax (name := enumcmd) declModifiers "enum" ident "where" item* optDeriving : command

@[macro enumcmd]
def elabEnum : Macro := fun stx => do match stx with
| `($modifiers:declModifiers enum $name:ident where $items:item* $dcs:optDeriving) => doit modifiers name items dcs
| _ => Macro.throwUnsupported
where
  doit (modifiers : TSyntax `Lean.Parser.Command.declModifiers)
       (name : TSyntax `ident)
       (items : TSyntaxArray `KLR.Util.item)
       (dcs : TSyntax `Lean.Parser.Command.optDeriving) : MacroM (TSyntax `command) := do
    let priv := ((modifiers.raw.getArg 2).getArg 0).getArg 0
    let isPrivate : Bool := match priv.getAtomVal with
    | "private" => true
    | _ => false
    let mut cmds : List (TSyntax `command) := []
    let mut unsortedValues : List (TSyntax `Lean.Parser.Command.ctor × TSyntax `num) := []
    let mut ctors : Array (TSyntax `Lean.Parser.Command.ctor) := #[]
    let mut numValues : Array Nat := #[]
    let mut current : Nat := 0 -- The next value to use for an un-numbered constructor
    for item in items do
      match item with
      | `(item| $_:ctor := $v:num) => do
        numValues := numValues.push v.getNat
      | _ => continue
    for item in items do
      match item with
      | `(item| $id:ctor := $v:num) => do
        unsortedValues := (id, v) :: unsortedValues
        ctors := ctors.push id
      | `(item| $id:ctor) => do
        let id := ⟨id⟩
        let (numValues', current') := nextNat numValues current
        numValues := numValues'
        current := current'
        unsortedValues := (id, Syntax.mkNumLit (toString current)) :: unsortedValues
        current := current + 1
        ctors := ctors.push id
      | e => throw (.error Syntax.missing s!"invalid enum item {e}")
    let values := unsortedValues.mergeSort fun (_, n1) (_, n2) => n1.getNat <= n2.getNat
    let nums := (values.map fun (_, n) => n.getNat)
    match hasDuplicate nums with
    | some k =>
      throw (.error Syntax.missing s!"Duplicate numeric values: {k}")
    | none =>
    let cmd <-
      `(
        $modifiers:declModifiers inductive $name where
          $[ $ctors ]*
        $dcs:optDeriving
      )
    cmds := cmd :: cmds
    let typeName := name.raw.getId
    let toUInt8Name := mkIdent (.str typeName "toUInt8")
    let mut cases : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
    let mut terms : Array (TSyntax `term) := #[]
    for (c, n) in values do
      -- TODO: How should I actually turn a ctor to a term?
      -- Sketchy to grab the 3rd field, but I saw this in dbg_trace:
      --     Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] []) `r (Command.optDeclSig [] []))
      let c := mkIdent (c.raw.getIdAt 3)
      terms := terms.push c
      let case <- `(matchAltExpr| | .$c => $n:num)
      cases := cases.push case
    -- TODO: Improve duplication
    let toUInt8 <- if isPrivate then `(
       private def $toUInt8Name:ident (x : $name) : UInt8 := match x with
        $cases:matchAlt*
    ) else `(
       def $toUInt8Name:ident (x : $name) : UInt8 := match x with
        $cases:matchAlt*
    )
    cmds := toUInt8 :: cmds
    let fromUInt8Name := mkIdent (.str typeName "fromUInt8")
    let mut cases1 : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
    for (c, n) in values do
      let c := mkIdent (c.raw.getIdAt 3)
      let case <- `(matchAltExpr| | $n:num => return .$c)
      cases1 := cases1.push case
    let other <- `(matchAltExpr| | n => throw ("Unexpected numeric code " ++ $(Lean.quote typeName.toString) ++ s!": {n} = {u8ToHex n}"))
    cases1 := cases1.push other
    -- TODO: Improve duplication
    let fromUInt8 <- if isPrivate then
     `(
        private def $fromUInt8Name:ident (x : UInt8) : Except String $name := match x with
          $cases1:matchAlt*
      )
      else
     `(
        def $fromUInt8Name:ident (x : UInt8) : Except String $name := match x with
          $cases1:matchAlt*
      )
    let valuesFunName := mkIdent (.str typeName "values")
    let valuesFun <- `(
      def $valuesFunName : List $name := [ $terms,* ]
    )
    let instances <- `(
      deriving instance BEq, DecidableEq, FromJson, FromSexp, Inhabited, Repr, ToJson, ToSexp for $name
    )
    let fromUInt8!Name : Lean.Ident := mkIdent (.str typeName "fromUInt8!")
    let n : Lean.Ident := Lean.mkIdent (.str .anonymous "n")
    let app : Lean.Term := Syntax.mkApp fromUInt8Name #[n]
    let fromUInt8! <- `(
      def $fromUInt8!Name:ident ($n : UInt8) : $name := match $app:term with
      | .ok v => v
      | .error msg => panic msg
    )
    let enumInstance <- `(
      instance : Enum $name where
        toUInt8 := $toUInt8Name
        fromUInt8 := $fromUInt8Name
    )
    let ltInstance <- `(
      instance : LT $name where
        lt a b := $toUInt8Name a < $toUInt8Name b
    )
    let ltDecidableInstance <- `(
      instance (a b : $name) : Decidable (a < b) :=
        UInt8.decLt ($toUInt8Name a) ($toUInt8Name b)
    )
    let leInstance <- `(
      instance : LE $name where
        le a b := $toUInt8Name a <= $toUInt8Name b
    )
    let leDecidableInstance <- `(
      instance (a b : $name) : Decidable (a <= b) :=
        UInt8.decLe ($toUInt8Name a) ($toUInt8Name b)
    )
    let toStringInstance <- `(
      instance : ToString $name where
        toString x := ((reprStr x).splitOn ".").reverse.head!
    )
    let mut cases2 : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
    for (c, _) in values do
      let c := mkIdent (c.raw.getIdAt 3)
      let cstr : TSyntax `str := Syntax.mkStrLit c.getId.toString
      let case <- `(matchAltExpr| | $cstr:str => some .$c)
      cases2 := cases2.push case
    let other <- `(matchAltExpr| | _ => none)
    cases2 := cases2.push other
    let fromStringName := mkIdent (.str typeName "fromString")
    let fromString <- `(
      def $fromStringName (s : String) : Option $name := match s with
        $cases2:matchAlt*
    )
    let res <- `(
      $cmd:command
      $instances
      $toUInt8
      $fromUInt8
      $fromUInt8!
      $enumInstance
      $ltInstance
      $ltDecidableInstance
      $leInstance
      $leDecidableInstance
      $toStringInstance
      $fromString
      $valuesFun
    )
    -- SM: Leave this in
    -- dbg_trace "{res.raw.prettyPrint}"
    return res

namespace Test

/-- Docstring -/
@[export foo]
private enum Foo where
  | x
  | y
  | z := 5
  | q := 1
  | r := 9
  | m := 10
  | n

#guard Enum.toUInt8 Foo.x == 0
#guard Foo.toUInt8 .x == 0
#guard Foo.x.toUInt8 == 0
#guard Foo.y.toUInt8 == 2
#guard Foo.n.toUInt8 == 3
#guard Foo.fromUInt8! Foo.x.toUInt8 == Foo.x
#guard Foo.fromUInt8! Foo.m.toUInt8 == Foo.m
#guard Foo.values == [.x, .q, .y, .n, .z, .r, .m]
#guard Foo.x < Foo.z
#guard Foo.x <= Foo.z
#guard toString Foo.x == "x"
#guard toJson Foo.x == Json.str "x"
#guard get! (fromJson? "x") == Foo.x
#guard Foo.fromString "x" == some Foo.x
#guard (Foo.fromString "k").isNone

private enum Bar where
  | x
  | y
  | z

#guard Bar.values == [.x, .y, .z]
#guard toSexp Bar.x == Sexp.atom "x"
#guard fromSexp? (Sexp.atom "x") == .ok Bar.x

end Test

end KLR.Util
