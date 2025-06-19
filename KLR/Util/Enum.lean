/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import TensorLib.Common
import Util.Hex
import Util.Sexp

open KLR.Util.Hex(encode)
open KLR.Util.Sexp(FromSexp ToSexp)
open Lean(FromJson Json Syntax TSyntax TSyntaxArray ToJson mkIdent fromJson? toJson)
open Lean.Elab.Command(CommandElab CommandElabM elabCommand liftTermElabM)
open Lean.Parser.Term(matchAltExpr)
open Lean.PrettyPrinter(ppCommand ppExpr ppTerm)
open TensorLib(get!)

syntax item := Lean.Parser.Command.ctor (":=" num)?
syntax items := manyIndent(item)
syntax (name := enumcmd) "private"? "enum" ident "where" items : command

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

@[command_elab enumcmd]
def elabEnum : CommandElab
| `(enum $name:ident where $items:item*) => doit false name items
| `(private enum $name:ident where $items:item*) => doit true name items
| _ => throwError "invalid enum syntax"
where
  doit (priv : Bool) (name : TSyntax `ident) (items : TSyntaxArray `item) : CommandElabM Unit := do
    let mut values : List (TSyntax `Lean.Parser.Command.ctor × TSyntax `num) := []
    let mut ctors : Array (TSyntax `Lean.Parser.Command.ctor) := #[]
    let mut numValues : Array Nat := #[]
    let mut current : Nat := 0 -- The next value to use for an un-numbered constructor
    for item in items do
      match item with
      | `(item| $_:ctor := $v:num) => do
        numValues := numValues.push v.getNat
      | _ => continue
    -- dbg_trace "numValues: {numValues}"
    for item in items do
      match item with
      | `(item| $id:ctor := $v:num) => do
        values := (id, v) :: values
        ctors := ctors.push id
      | `(item| $id:ctor) => do
        let id := ⟨id⟩
        let (numValues', current') := nextNat numValues current
        numValues := numValues'
        current := current'
        values := (id, Syntax.mkNumLit (toString current)) :: values
        current := current + 1
        ctors := ctors.push id
      | e => throwError s!"invalid enum item {e}"
    let nums := (values.map fun (_, n) => n.getNat)
    match hasDuplicate nums with
    | some k =>
      throwError s!"Duplicate numeric values: {k}"
    | none =>
    let cmd <- if priv then
      `(
        private inductive $name where
          $[ $ctors ]*
      )
    else
      `(
        inductive $name where
          $[ $ctors ]*
      )
    elabCommand cmd
    let typeName := name.raw.getId
    let toUInt8Name := mkIdent (.str typeName "toUInt8")
    let mut cases : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
    let mut terms : Array (TSyntax `term) := #[]
    -- let nums' : Array Nat := nums.map fun n => n.
    for (c, n) in values do
      -- TODO: How should I actually turn a ctor to a term?
      -- Sketchy to grab the 3rd field, but I saw this in dbg_trace:
      --     Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] []) `r (Command.optDeclSig [] []))
      let c := mkIdent (c.raw.getIdAt 3)
      terms := terms.push c
      let case <- `(matchAltExpr| | $c => $n:num)
      cases := cases.push case
    terms := terms.insertionSort fun x y => x.raw.getId.toString < y.raw.getId.toString
    let toUInt8 <- `(
      private def $toUInt8Name:ident (x : $name) : UInt8 := match x with
        $cases:matchAlt*
    )
    elabCommand toUInt8
    let fromUInt8Name := mkIdent (.str typeName "fromUInt8")
    let mut cases1 : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
    for (c, n) in values do
      let c := mkIdent (c.raw.getIdAt 3)
      let case <- `(matchAltExpr| | $n:num => return .$c)
      cases1 := cases1.push case
    let other <- `(matchAltExpr| | n => throw ("Unexpected numeric code " ++ $(Lean.quote typeName.toString) ++ s!": {n} = {u8ToHex n}"))
    cases1 := cases1.push other
    let fromUInt8 <- `(
      private def $fromUInt8Name:ident (x : UInt8) : Except String $name := match x with
        $cases1:matchAlt*
    )
    elabCommand fromUInt8
    let valuesFunName := mkIdent (.str typeName "values")
    let valuesFun <- `(
      def $valuesFunName : List $name := [ $terms,* ]
    )
    -- SM: Leave this in as an example
    -- dbg_trace (<- liftTermElabM <| ppCommand valuesFun)
    elabCommand valuesFun
    let instances <- `(
      deriving instance BEq, DecidableEq, FromJson, FromSexp, Inhabited, Repr, ToJson, ToSexp for $name
    )
    elabCommand instances
    let fromUInt8!Name : Lean.Ident := mkIdent (.str typeName "fromUInt8!")
    let n : Lean.Ident := Lean.mkIdent (.str .anonymous "n")
    let app : Lean.Term := Syntax.mkApp fromUInt8Name #[n]
    let fromUInt8! <- `(
      def $fromUInt8!Name:ident ($n : UInt8) : $name := match $app:term with
      | .ok v => v
      | .error msg => panic msg
    )
    elabCommand fromUInt8!
    let enumInstance <- `(
      instance : Enum $name where
        toUInt8 := $toUInt8Name
        fromUInt8 := $fromUInt8Name
    )
    elabCommand enumInstance
    let ltInstance <- `(
      instance : LT $name where
        lt a b := a.toUInt8 < b.toUInt8
    )
    elabCommand ltInstance
    let ltDecidableInstance <- `(
      instance (a b : $name) : Decidable (a < b) :=
        UInt8.decLt a.toUInt8 b.toUInt8
    )
    elabCommand ltDecidableInstance
    let leInstance <- `(
      instance : LE $name where
        le a b := a.toUInt8 <= b.toUInt8
    )
    elabCommand leInstance
    let leDecidableInstance <- `(
      instance (a b : $name) : Decidable (a <= b) :=
        UInt8.decLe a.toUInt8 b.toUInt8
    )
    elabCommand leDecidableInstance
    let toStringInstance <- `(
      instance : ToString $name where
        toString x := ((reprStr x).splitOn ".").reverse.head!
    )
    elabCommand toStringInstance

section Test

private enum Foo where
  | x
  | y
  | z := 5
  | q := 1
  | r := 9
  | m := 10
  | n

#guard Foo.x.toUInt8 == 0
#guard Foo.y.toUInt8 == 2
#guard Foo.n.toUInt8 == 3
#guard Foo.fromUInt8! Foo.x.toUInt8 == Foo.x
#guard Foo.fromUInt8! Foo.m.toUInt8 == Foo.m
#guard Foo.values == [.m, .n, .q, .r, .x, .y, .z]
#guard Foo.x < Foo.z
#guard Foo.x <= Foo.z
#guard toString Foo.x == "x"
#guard toJson Foo.x == Json.str "x"
#guard get! (fromJson? "x") == Foo.x

private enum Bar where
  | x
  | y
  | z

#guard Bar.values == [.x, .y, .z]
#guard Sexp.toSexp Bar.x == Sexp.atom "x"
#guard Sexp.fromSexp Bar (Sexp.atom "x") == .ok Bar.x

end Test

end KLR.Util
