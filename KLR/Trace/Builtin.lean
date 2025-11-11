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

-- Build names in the nki namespaces

def nki_ : Name := .str .anonymous "nki"
def nki_isa : Name := .str nki_ "isa"
def nki_stdlib : Name := .str nki_ "stdlib"
def nki_lang : Name := .str nki_ "language"
def nki_typing : Name := .str nki_ "typing"

def nl : String -> Name := .str nki_lang
def nisa : String -> Name := .str nki_isa
def nt : String -> Name := .str nki_typing

def numpy : Name := .str .anonymous "numpy"

-- conveience functions for creating environment entries

def module (name : Name) : Name × Term :=
  (name, .module name)

def const_var (name: Name) : Name × Term :=
  (name, .var name)

def const_int (name: Name) (i : Int) : Name × Term :=
  (name, .int i)

-- Type of builtin functions; since these are called from python,
-- they take a list of positional argument and a list of keyword
-- arguments.
abbrev BuiltinFn := List Term -> List (String × Term) -> Trace Term

/-
This function is used by the nki macro (see below) to convert
Python arguments to Lean arguments.
-/

partial def resolveRefs (t : Term) : Trace Term :=
  match t with
  | .ref name _ => do resolveRefs (<- lookup name)
  | .tuple l => return .tuple (<- l.mapM resolveRefs)
  | .list l => return .list (<- l.mapM resolveRefs)
  | .dict l => return .dict (<- l.mapM fun (s,t) => return (s, <- resolveRefs t))
  | _ => return t

private class Resolve (a : Type) extends FromNKI a where
  resolve : Term -> Trace a

instance [FromNKI a] : Resolve a where
  resolve t := do fromNKI? (<- resolveRefs t)

instance : Resolve Term where
  resolve t := pure t

def getArg (a : Type) [Resolve a]
           (fnName : String)
           (args : List Term)
           (kw : List (String × Term))
           (pos : Nat) (name : String) (dflt : Option a) : Trace a := do
  if h:pos < args.length then
    try
      Resolve.resolve (args[pos]'h)
    catch e =>
      throw s!"Failed to resolve an argument '{name}', {e}"
  else
    match kw.find? fun (n,_) => n == name with
    | .some (_,x) => do
      try
        Resolve.resolve x
      catch e =>
        throw s!"Failed to resolve an argument '{name}', {e}"
    | .none => match dflt with
              | .some a => return a
              | .none => throw s!"argument '{name}' not found, in builtin function '{fnName}'"

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

private def registerBuiltin (name : TSyntax `ident) : CommandElabM Ident := do
  let nkiName := name.getId
  let nkiName' := nkiName.toString.replace "." "_"
  let leanName := Name.str (<- getCurrNamespace) nkiName'
  let name := mkIdent (Name.str .anonymous nkiName')
  modifyEnv fun env =>
    extension.addEntry env { nkiName, leanName : Builtin }
  return name

@[command_elab nkicmd]
def klrElab : CommandElab
  | `(nki $name (args : List Term) := do $rhs*) => do
    let name <- registerBuiltin name
    let cmd <- `(
      def $name ($(mkIdent `args) : List Term) (kw : List (String × Term)) : Trace Term := do
        $[$rhs]*
    )
    elabCommand cmd
  | `(nki $name $args* := do $rhs*) => do
    let name <- registerBuiltin name
    let (ids, tys, dflts) <- elabArgs args
    let pos := ((List.range ids.size).map Syntax.mkNatLit).toArray
    let names := ids.map idToStrLit
    let validNames := ids.map idToStrLit
    let cmd <- `(
      def $name (args : List Term) (kw : List (String × Term)) : Trace Term := do
        let fnName := $(idToStrLit name)
        let validNames := [$validNames,*]
        let _ <- kw.foldlM (fun _ (kwName, _) => do
          if !validNames.contains kwName then
            throw s!"unexpected keyword argument '{kwName}' in builtin function '{fnName}'"
          return ()) ()
        $[let $ids <- getArg $tys fnName args kw $pos $names $dflts]*
        $[$rhs]*
    )
    elabCommand cmd
  | _ => throwError s!"invalid NKI syntax"
