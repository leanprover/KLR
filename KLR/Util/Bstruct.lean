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


/-
A bstruct allows packing several fields into s single UInt8, with
automatic conversions between the byte and the struct. Each type T
in the bstruct must have

  T.toUint8 : T -> UInt8
  T.fromUInt8 : UInt8 -> Err String T

For example,

enum E where
| x := 0x01
| y := 0x07

bstruct Foo where
  x : E : 5
  y : UInt8 : 2
  z : UInt16 : 1

is equivalent to

structure Foo where
  x : E
  y : UInt8
  z : UInt16
deriving BEq, DecidableEq, FromJson, FromSexp, Inhabited, Repr, ToJson, ToSexp

instance : NumBytes Foo where
  numBytes _ := 1

instance : ToBytes Foo where
  toBytes s :=
    let b := borList [
      ((s.x.toUInt8 &&& 0b11111) <<< 3),
      ((s.y.toUInt8 &&& 0b11) <<< 1),
      ((s.z.toUInt8 &&& 0b1) <<< 0),
    ]
    ⟨ #[b] ⟩

instance : FromBytes Foo where
  fromBytesUnchecked arr := do
    let (b, rest) := arr.splitAt 1
    let b := b[0]!
    let x := (b >>> 3) &&& 0b11111
    let y := (b >>> 1) &&& 0b11
    let z := b &&& 0b1
    (Foo.mk (<- fromUInt8 x) (<- fromUInt8 y) (<- fromUInt8 z), rest)

TODO: Generalize to multiple bytes
TODO: Check the sizes of inputs to `mk` to ensure they don't overflow the bits
-/
import Lean
import Plausible
import TensorLib.Common
import Util.Enum
import Util.FromBytes
import Util.NumBytes
import Util.ToBytes
import Util.Sexp

open KLR.Util(FromBytes FromSexp NumBytes ToBytes ToSexp)
open Lean(FromJson Json Syntax TSyntax TSyntaxArray ToJson mkIdent fromJson? toJson)
open Lean.Elab.Command(CommandElab CommandElabM elabCommand liftTermElabM)
open Lean.Parser.Command(declModifiers)
open Lean.Parser.Term(matchAltExpr)
open Lean.PrettyPrinter(ppCommand ppExpr ppTerm)
open TensorLib(get!)

namespace KLR.Util.Bstruct

open Lean(Name)
open Lean.Parser.Command
open Lean.Parser.Term

syntax item := ident ":" ident ":=" num
syntax items := manyIndent(item)
syntax (name := bstructcmd) declModifiers "bstruct" ident "where" item* optDeriving : command

def _root_.UInt8.toUInt8 (n : UInt8) : UInt8 := n
def _root_.UInt8.fromUInt8 (n : UInt8) : Err UInt8 := pure n
def _root_.UInt16.fromUInt8 (n : UInt16) : Err UInt8 := pure n.toUInt8
def _root_.UInt32.fromUInt8 (n : UInt32) : Err UInt8 := pure n.toUInt8
def _root_.UInt64.fromUInt8 (n : UInt64) : Err UInt8 := pure n.toUInt8

private def borList (ns : List UInt8) (acc : UInt8 := 0) : UInt8 := match ns with
| [] => acc
| n :: ns => borList ns (n ||| acc)

#guard borList [0b00100, 0b10000, 0b00001] == 0b10101

-- (s.f &&& n) <<< m
private def andShift (struct : Name) (field : Name) (and : UInt8) (shift : UInt8) : CommandElabM (TSyntax `term) := do
  let f := mkIdent ((struct.append field).append `toUInt8)
  let and := Lean.Syntax.mkNumLit (toString and)
  let shift := Lean.Syntax.mkNumLit (toString shift)
  `(($f &&& $and) <<< $shift)

private def toBytes (struct : Name) (fields : Array (Name × Name × UInt8)) : CommandElabM (TSyntax `term) := do
  let mut sum := 0
  let mut terms := #[]
  for (field, _, bits) in fields do
    sum := sum + bits
    let shift := 8 - sum
    let and := (2 ^ bits.toNat) - 1
    let t <- andShift struct field and shift
    terms := terms.push t
  let body <- `(borList [ $[ $terms ],* ])
  `(⟨ #[$body] ⟩)

-- (byte >>> n) &&& m
private def andShift' (type : Name) (byte : Name) (shift : UInt8) (and : UInt8) : CommandElabM (TSyntax `term) := do
  let fromUInt8 := mkIdent (type.append `fromUInt8)
  let byte := mkIdent byte
  let and := Lean.Syntax.mkNumLit (toString and)
  let shift := Lean.Syntax.mkNumLit (toString shift)
  `($fromUInt8 (($byte >>> $shift) &&& $and))

private def fromBytes (byte : Name) (fields : Array (Name × Name × UInt8)) : CommandElabM (TSyntax `term) := do
  let mut sum := 0
  let mut terms := #[]
  for (_, typ, bits) in fields do
    sum := sum + bits
    let shift := 8 - sum
    let and := (2 ^ bits.toNat) - 1
    let t <- andShift' typ byte shift and
    terms := terms.push t
  `( ⟨ $[ <- $terms ],*  ⟩ )

@[command_elab bstructcmd]
def elabEnum : CommandElab
| `($modifiers:declModifiers bstruct $name:ident where $items:item* $dcs:optDeriving) =>
  doit modifiers name items dcs
| _ => throwError "invalid bstruct syntax"
where
  doit (modifiers : TSyntax `Lean.Parser.Command.declModifiers)
       (name : TSyntax `ident)
       (items : TSyntaxArray `KLR.Util.Bstruct.item)
       (dcs : TSyntax `Lean.Parser.Command.optDeriving) : CommandElabM Unit := do
    let mut fields : Array (Name × Name × UInt8) := #[]
    let mut sfields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder) := #[]
    for item in items do
      match item with
      | `(item| $x:ident : $typ := $v:num) =>
        fields := fields.push (x.getId, typ.getId, v.getNat)
        sfields := sfields.push (<- `(structSimpleBinder| $x:ident : $typ))
      | _ => throwError "illegal syntax"
    let cmd <-
      `(
        $modifiers:declModifiers structure $name where
          $[ $sfields ]*
        $dcs:optDeriving
      )
    if (fields.map fun (_, _, n) => n.toNat).sum != 8 then throwError "bstruct fields need to sum to 8"
    -- SM: Leave this in
    -- dbg_trace (<- liftTermElabM <| ppCommand cmd)
    elabCommand cmd
    let instances <- `(
      deriving instance BEq, DecidableEq, FromSexp, Inhabited, Repr, ToSexp for $name
    )
    elabCommand instances
    let numBytesInstance <- `(
      instance : NumBytes $name where
        numBytes _ := 1
    )
    elabCommand numBytesInstance
    let s : TSyntax `ident := mkIdent `s
    let toBytesInstance <- `(
      instance : ToBytes $name where
        toBytes ($s : $name) := $(<- toBytes `s fields)
    )
    -- SM: Leave this in
    -- dbg_trace (<- liftTermElabM <| ppCommand toBytesInstance)
    elabCommand toBytesInstance
    let b : TSyntax `ident := mkIdent `b
    let body <- fromBytes `b fields
    let fromBytesInstance <- `(
      instance : FromBytes $name where
        fromBytesUnchecked (arr : ByteArray) := do
          let ($b, rest) := arr.splitAt 1
          let $b := $b[0]!
          return ($body, rest)
    )
    -- SM: Leave this in
    -- dbg_trace (<- liftTermElabM <| ppCommand fromBytesInstance)
    elabCommand fromBytesInstance

section Test

private enum E where
| x := 5
| y := 7

-- /-- Docstring -/
@[export foo]
private bstruct Foo where
  x : E := 5
  y : UInt8 := 2
  z : UInt8 := 1
deriving Repr

#guard ToBytes.toBytes (Foo.mk E.x 3 1) == ByteArray.mk #[ 5 <<< 3 ||| 3 <<< 1 ||| 1 ]

private bstruct Foo0 where
  x : UInt8 := 8

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (n : UInt8) : ToBytes.toBytes (Foo0.mk n) == ⟨ #[n] ⟩ := by plausible

private bstruct Foo1 where
  x : UInt8 := 4
  y : UInt8 := 4

def UInt4 := UInt8
deriving Repr

def roundTrip (n m : UInt4) : Bool :=
  let foo := Foo1.mk n m
  KLR.Util.fromBytes Foo1 (ToBytes.toBytes foo) == .ok (foo, ByteArray.empty)

#guard ToBytes.toBytes (Foo1.mk 3 4) == ⟨ #[ (3 <<< 4) ||| 4 ] ⟩
#guard
  let foo := Foo1.mk 10 4
  KLR.Util.fromBytes Foo1 (ToBytes.toBytes foo) == .ok (foo, ByteArray.empty)

private def u4Gen : Plausible.Gen UInt4 := do
  let n <- Plausible.Gen.choose Nat 0 15 (by omega)
  return n.val.toUInt8

instance : Plausible.Shrinkable UInt4 where
  shrink n := [n]

instance : Plausible.SampleableExt UInt4 :=
  Plausible.SampleableExt.mkSelfContained u4Gen

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (n m : UInt4) : ToBytes.toBytes (Foo1.mk m n) == ⟨ #[ m.toNat <<< 4 ||| n.toNat ] ⟩ := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (n m : UInt4) : roundTrip n m := by plausible

end Test
