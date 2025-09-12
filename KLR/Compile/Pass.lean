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

import KLR.Core.Basic
import KLR.Util

/-
# Basic structure of a Compiler Pass
-/

namespace KLR.Compile.Pass
export Core (Name Pos)

/-
# Assigning Source Locations to Errors and Warnings

During a translation pass, errors and warnings are created using `throw` and
`warn`. These functions create a "raw message" which only contains the text of
the message. The `withPos p m` function is used to assign a source location,
`p` any messages emitted by the monadic code, `m`. Upon return from `withPos`
all messages are converted from raw messages to "located" messages which have a
source location attached to them.

Because the parser only deals with single functions, the source locations
assigned by `withPos` are relative to the start of the function body (each
function has a starting line of 1). The `withFile` function is used to assign a
filename and absolute position within the file to each message. Upon return
from `withFile` all messages are converted to "absolute" messages which have a
filename and absolute position within the file attached to each message.

A typical use looks like:

```
do
  ...
  withFile file line_offset do
    ...
    withPos pos1 do ...
      ...
      withPos pos2 do ...
```

The filename, line offset, and positions are found in the abstract syntax tree
that is being processed. In the case of nested `withFile` or `withPos`, the
inner-most call will assign the location information: these functions will
ignore any messages that already have source locations attached.
-/

inductive PosError where
  | raw (msg : String)
  | located (pos : Pos) (msg : String)
  | absolute (file : String) (pos : Pos) (msg : String)
  | formatted (msg : String)
  deriving Inhabited, Repr

namespace PosError

def msg : PosError -> String
  | .raw msg | .located _ msg | .absolute _ _ msg | .formatted msg => msg

def locate (pos : Pos) (pe : PosError) : PosError :=
  match pe with
  | .raw s => .located pos s
  | .located ..
  | .absolute ..
  | .formatted .. => pe  -- do not change already located messages

def addFile (file : String) (lineOffset : Nat) : PosError -> PosError
  | .raw msg => .absolute file { line := lineOffset } msg
  | .located pos msg => .absolute file { pos with line := pos.line + lineOffset } msg
  | err => err  -- do not change already located message

-- Note: This format should be understandable by upstream tools and callers
instance : ToString PosError where
  toString
    | .raw m => m
    | .located p m => s!"{p.line}:{p.column}:{m}"
    | .absolute f p m => s!"{f}:{p.line}:{p.column}:{m}"
    | .formatted m => s!"{m}"

end PosError

/-
A simple utility monad which contains state that is generally useful for
compiler passes.
-/
structure PassState where
  freshVarNum : Nat := 0 -- counter for generating fresh names
  pos : Pos  := { line := 0 }
  lineOffset : Nat := 0 -- offset to convert relative to absolute line numbers
  warnings : Array PosError := #[]  -- located warnings
  newWarns : Array PosError := #[]  -- raw warnings

namespace PassState

/-
When a new warning is emitted, it is initially unlocated and goes into the
`newWarns` array to indicate that it needs to be located.
-/
def warn (msg : String) (ps : PassState) : PassState :=
  { ps with
    newWarns := ps.newWarns.push (.raw msg)
  }

/-
When we `locate` a state, all new warnings are given the same position and
moves to the `warnings` array of located warnings.
-/
def locate (pos : Pos) (ps : PassState) : PassState :=
  { ps with
    warnings := ps.warnings.append (ps.newWarns.map (.locate pos))
    newWarns := #[]
  }

/-
When we add a file name, we first locate any unlocated warnings, and then we
add a filename to any warnings without one.
The order of operations is: warn, locate, addFile.
-/
def addFile (file : String) (lineOffset : Nat) (ps : PassState) : PassState :=
  { ps.locate { line := lineOffset, column := 0 } with
    warnings := ps.warnings.map (.addFile file lineOffset)
  }

/-
We should always have at least one `locate` or `addFile` at the outermost
level, or we may lose warnings trapped in the `newWarn` array. The `finalize`
function can be used to make sure all warnings are moved over.
-/
def finalize (file : String) (ps : PassState) : PassState :=
  addFile file 0 ps

end PassState

abbrev PassM := EStateM PosError PassState

namespace PassM

instance : MonadExceptOf String PassM where
  throw msg := throw (.raw msg)
  tryCatch m f := tryCatch m (fun e => match e with
    | .formatted _ => throw e
    | _ => f e.msg
  )

-- get the current source position
def getPos : PassM Pos := do
  let s <- get
  let pos := s.pos
  return { pos with line := pos.line + s.lineOffset - 1 }

def withPos (pos : Pos) (m : PassM a) : PassM a :=
  fun s => match m { s with pos := pos } with
    | .ok x s => .ok x (s.locate pos)
    | .error e s => .error (e.locate pos) (s.locate pos)

def withFile (file : String) (lineOffset : Nat) (source : String) (m : PassM a) : PassM a := do
  let s <- get
  let p' := { s.pos with filename := some file }
  fun s => match m { s with pos := p', lineOffset := lineOffset } with
    | .ok x s =>
        .ok x { s with pos := p' }
    | .error (.raw msg) s =>
        .error (.formatted (genError msg file lineOffset source s.pos)) { s with pos := p' }
    | .error (.located pos msg) s =>
        .error (.formatted (msg ++ genError msg file lineOffset source pos)) { s with pos := p' }
    | .error (.absolute f pos msg) s =>
        .error (.formatted (genError msg f lineOffset source pos)) { s with pos := p' }
    | .error (.formatted msg) s =>
        .error (.formatted (msg ++ genError "called from" file lineOffset source s.pos)) { s with pos := p' }
where
  genError (msg : String) (f: String) (offset : Nat) (source : String) (pos : Pos) : String :=
    let lines := source.splitOn "\n"
    let lineno := pos.line - 1
    let colno := pos.column
    let line := if h:lineno < lines.length
                then lines[lineno]'h
                else "<source not available>"
    let indent := (Nat.repeat (List.cons ' ') colno List.nil).asString
    s!"\n{f}:{lineno + offset}:\n{line}\n{indent}^-- {msg}"


end PassM

/-
Generate a fresh name, based on a previous name. Users can not create names
with numeric components, so these will not conflict with user names.
-/
def freshName (name : Name := `tmp) : PassM Name :=
  modifyGet fun s =>
    let n := s.freshVarNum + 1
    (.num name n, { s with freshVarNum := n })

-- Emit a warning / linter message
def warn (msg : String) : PassM Unit :=
  modify (PassState.warn msg)

/-
PassM will often be used within a monad transformer, so we provide "unlifted"
versions of the monad utilities for convenience. Note: The standard library
provides MonadControl instances for the common monads and monad transformers.
-/

def withPos [Monad m] [MonadControlT PassM m]
            (pos : Pos) (x : m a) : m a :=
  control fun mapInBase => (PassM.withPos pos) (mapInBase x)

def withFile [Monad m] [MonadControlT PassM m]
             (file : String) (lineOffset : Nat) (source : String) (x : m a) : m a :=
  control fun mapInBase => (PassM.withFile file lineOffset source) (mapInBase x)

def getPos [Monad m] [MonadControlT PassM m] : m Pos :=
  liftWith fun _ => PassM.getPos

-- Passes will commonly want to add more state
abbrev Pass st := StateT st PassM
