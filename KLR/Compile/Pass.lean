/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core.Basic
import KLR.Util

/-
# Basic structure of a Compiler Pass
-/

namespace KLR.Compile.Pass
export Core (Pos)

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

TODO: This monad is useful in lots of places, should live somewhere else.
-/

inductive PosError where
  | raw (msg : String)
  | located (pos : Pos) (msg : String)
  | absolute (file : String) (pos : Pos) (msg : String)
  deriving Inhabited, Repr

namespace PosError

def msg : PosError -> String
  | .raw msg | .located _ msg | .absolute _ _ msg => msg

def locate (pos : Pos) (pe : PosError) : PosError :=
  match pe with
  | .raw s => .located pos s
  | .located ..
  | .absolute .. => pe  -- do not change already located messages

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

end PosError

structure PosState where
  warnings : Array PosError := #[]  -- located warnings
  newWarns : Array PosError := #[]  -- raw warnings

namespace PosState

/-
When a new warning is emitted, it is initially unlocated and goes into the
`newWarns` array to indicate that it needs to be located.
-/
def warn (msg : String) (ps : PosState) : PosState :=
  { ps with
    newWarns := ps.newWarns.push (.raw msg)
  }

/-
When we `locate` a state, all new warnings are given the same position and
moves to the `warnings` array of located warnings.
-/
def locate (pos : Pos) (ps : PosState) : PosState :=
  { ps with
    warnings := ps.warnings.append (ps.newWarns.map (.locate pos))
    newWarns := #[]
  }

/-
When we add a file name, we first locate any unlocated warnings, and then we
add a filename to any warnings without one.
The order of operations is: warn, locate, addFile.
-/
def addFile (file : String) (lineOffset : Nat) (ps : PosState) : PosState :=
  { ps.locate { line := lineOffset, column := 0 } with
    warnings := ps.warnings.map (.addFile file lineOffset)
  }

/-
We should always have at least one `locate` or `addFile` at the outermost
level, or we may lose warnings trapped in the `newWarn` array. The `finalize`
function can be used to make sure all warnings are moved over.
-/
def finalize (file : String) (ps : PosState) : PosState :=
  addFile file 0 ps

end PosState

abbrev PosM := EStateM PosError PosState

namespace PosM

instance : MonadExceptOf String PosM where
  throw msg := throw (.raw msg)
  tryCatch m f := tryCatch m (fun e => f e.msg)

def withPos (pos : Pos) (m : PosM a) : PosM a :=
  fun s => match m s with
    | .ok x s => .ok x (s.locate pos)
    | .error e s => .error (e.locate pos) (s.locate pos)

def withFile (file : String) (lineOffset : Nat) (m : PosM a) : PosM a :=
  fun s => match m s with
    | .ok x s => .ok x (s.addFile file lineOffset)
    | .error e s => .error (e.addFile file lineOffset) (s.addFile file lineOffset)

end PosM

-- Emit a warning / linter message
def warn (msg : String) : PosM Unit :=
  modify (PosState.warn msg)

/-
PosM will often be used within a monad transformer, so we provide "unlifted"
versions of `withPos` and `withFile` for convenience. Note: The standard library
provides MonadControl instances for the common monads and monad transformers.
-/

def withPos [Monad m] [MonadControlT PosM m]
            (pos : Pos) (x : m a) : m a :=
  control fun mapInBase => (PosM.withPos pos) (mapInBase x)

def withFile [Monad m] [MonadControlT PosM m]
             (file : String) (lineOffset : Nat) (x : m a) : m a :=
  control fun mapInBase => (PosM.withFile file lineOffset) (mapInBase x)

abbrev PassM st := StateT st PosM

