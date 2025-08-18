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

import KLR.Core
import KLR.Trace.Extension
import KLR.Trace.FromNKI
import KLR.Trace.Types

/-
# Utilities for creating Builtins
-/

namespace KLR.Trace
open KLR.Core
open Lean Elab Command Term Meta

-- Use numeric names to create names that can't be spelled by users
-- This is mainly used to model object methods (see below)
private def hidden (str : String) : Name := .num str.toName 0

-- Build names in the nki namespaces

def neuronxcc : Name := .str .anonymous "neuronxcc"
def nki_ : Name := .str neuronxcc "nki"
def nki_isa : Name := .str nki_ "isa"
def nki_lang : Name := .str nki_ "language"

def nl : String -> Name := .str nki_lang
def nisa : String -> Name := .str nki_isa

/-
Special names for object methods

In order to model built-in objects, we use Term.builtin with the optional extra
Term value. For example, if a user has a Term.pointer, say called "sbuf", then
they can call the method view `sbuf.view(...)`. This expression is an attribute
projection of "view" followed by a call of whatever the projection returns.

In response to the projection of "view" from Term.pointer, we return a builtin
with the pointer embedded in it:

  (pointer a).view  ==>  builtin name type (pointer a)

Later when we get a call to this builtin, it is transformed to:

  call (builtin name type (pointer a)) args => (lookup name) (pointer a) args

So, we need a name to refer to the implementation of the builtin object method
view. We do not want users to be able to call this method, so we use hidden
names, which are just names that would be syntactically invalid in python.

We define all of these special names here.
-/

def memPtrName := `builtin.memPtr
def memPtrBuiltin (a : Address) : Term :=
  .builtin memPtrName (some (.pointer a))

def memViewName := `builtin.memView
def memViewBuiltin (a : Address) : Term :=
  .builtin memViewName (some (.pointer a))

def reshapeName := `builtin.reshape
def reshapeBuiltin (t : Term) : Term :=
  .builtin reshapeName (some t)

-- conveience functions for creating environment entries

def module (name : Name) : Name × Term :=
  (name, .module name)

def const_var (name: Name) : Name × Term :=
  (name, .expr (.value $ .var name.toString))

def const_int (name: Name) (i : Int) : Name × Term :=
  (name, .expr (.value $ .int i))

-- Type of builtin functions; since these are called from python,
-- they take a list of positional argument and a list of keyword
-- arguments.
abbrev BuiltinFn := List Term -> List (String × Term) -> Trace Term

/-
This function is used by the nki macro (see below) to convert
Python arguments to Lean arguments.
-/

def fromNKIOpt [FromNKI a] (opt : Option a) (t : Term) : Err a :=
  match opt with
  | .none => fromNKI? t
  | .some a => return (fromNKI a t)

def getArg (a : Type) [FromNKI a]
           (args : List Term)
           (kw : List (String × Term))
           (pos : Nat) (name : String) (dflt : Option a) : Err a := do
  if h:pos < args.length then
    fromNKIOpt dflt (args[pos]'h)
  else
    match kw.find? fun (n,_) => n == name with
    | .some (_,x) => fromNKIOpt dflt x
    | .none => match dflt with
              | .some a => return a
              | .none => throw s!"argument {name} not found"

/-

The code below implements the nki command. The `nki` command is meant to be
used like `def`. For example, the code below:

nki f (a : Bool) (b : Int := 1) := do
  return .none

will be transformed to:

def f (args : List Term) (kw : List (String × Term)) : Trace Term := do
  let a <- getArg Bool args kw 0 "a" none
  let b <- getArg Int  args kw 1 "b" (some 1)
  return .none

Note: you must write "nki ... := do" for the elaborator to match on the syntax
(you have to start the body with "do"), this could be made more general if
necessary.
-/

syntax arg := "(" ident ":" term (":=" term)? ")"
syntax (name := nkicmd) "nki" ident arg* ":=" doElem : command

abbrev SynIdent := TSyntax `ident
abbrev SynTerm := TSyntax `term
abbrev SynArg := TSyntax `KLR.Trace.arg

-- Convert an identifier to a string literal
-- Note: this is a compile-time function, so panic is "OK"
def idToStrLit (tstx : SynIdent) : SynTerm :=
  match tstx.raw with
| .ident _ _ id _ => Syntax.mkStrLit id.toString
| _ => panic! "invalid call to idToStrLit"


-- deconstruct a argument (syntax arg) into its components
def elabArg : SynArg -> CommandElabM (SynIdent × SynTerm × SynTerm)
  | `(arg|($name : $type )) => return (name, type, <- ``(Option.none))
  | `(arg|($name : $type := $val)) => return (name, type, <- ``(Option.some $val))
  | _ => throwError "bad arg syntax"

-- deconstruct an array of arguments into parallel arrays of their components.
-- These arrays will supply the arguments to `getArg`.
def elabArgs (args : Array SynArg) :
             CommandElabM (Array SynIdent × Array SynTerm × Array SynTerm) := do
  let mut ids := #[]
  let mut types := #[]
  let mut defaults := #[]
  for arg in args do
      let (id, type, dflt) <- elabArg arg
      ids := ids.push id
      types := types.push type
      defaults := defaults.push dflt
  return (ids, types, defaults)

-- The main elaborator for the nki commmand

@[command_elab nkicmd]
def klrElab : CommandElab
  | `(nki $name $args* := do $rhs*) => do
    let nkiName := name.getId
    let nkiName' := nkiName.toString.replace "." "_"
    let leanName := Name.str (<- getCurrNamespace) nkiName'
    let name := mkIdent (Name.str .anonymous nkiName')
    modifyEnv fun env =>
      extension.addEntry env { nkiName, leanName : Builtin }
    let (ids, tys, dflts) <- elabArgs args
    let pos := ((List.range ids.size).map Syntax.mkNatLit).toArray
    let names := ids.map idToStrLit
    let cmd <- `(
      def $name (args : List Term) (kw : List (String × Term)) : Trace Term := do
        $[let $ids <- getArg $tys args kw $pos $names $dflts]*
        $[$rhs]*
    )
    elabCommand cmd
  | _ => throwError s!"invalid NKI syntax"
