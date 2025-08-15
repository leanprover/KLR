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
import KLR.Util
import KLR.Core
import KLR.NKI.Basic

/-
# Basic types for tracing

Tracing is a special form of partial evaluation. After parsing the original
python terms, they are "traced" to produce simpler KLR terms. Therefore the
input to tracing is a `KLR.Python` AST, and the output is a `KLR.Core` AST. The
tracing process introduces an intermediate AST, called `Term` which is an
extension of the `KLR.Expr` type. The `Term` type is used to represent
sub-expressions that are in the process of being traced, but not yet
representable in KLR. For example, consider the statement:

  a, b = t.shape

Here, the left-hand side is a tuple of variables (which cannot be represented in
KLR), and the right-hand side is a built-in attribute of a tensor. During
tracing, the expression elaborator needs to return a tuple of variables `(a,b)`,
and the built-in `shape` attribute needs to return a tuple of integers. With
both of these in hand, the statement elaborator can expand the tuples into two
KLR assignment statements (or generate an error). The intermediate tuples are
elements of the type `Term`, and the final statements are elements of the type
`KLR.Stmt`.

Tracing takes place within a state monad called `Trace`. The `Trace` monad
provides access to an environment which contains bindings for all of the local
variables currently in scope. All local variables refer to `Term`s and hence
may not be fully reduced. At the completion of tracing, all terms must be
reducible to `KLR.Expr`s or an error is generated. This requirement is due to
an implicit phase separation in the design of NKI: some terms must be
eliminated by tracing, and some terms can be passed to the compiler. KLR only
represents terms which can be passed on to the compiler. For example,
assertions have to be resolved at tracing time, neither the compiler nor the
hardware can raise an assertion that the user can see during development.
Hence, KLR does not have an assert statement, and any expressions under an
assert must be resolved during tracing. Other examples are conditional
expressions, and loop bounds; both of which must be resolved during tracing.

In addition to `Term`s, the environment may contain references to built-in
objects. Built-in objects are defined using Lean functions that generate terms.
The set of built-ins is fixed by the implementation and cannot be changed at
runtime. This restriction could be lifted, but for now this is not necessary.

This module defines types to represent the built-ins, the environments, and the
tracing monads.
-/

namespace KLR.Trace
open KLR.Core
export Core (Name)

-- Bring in some NKI types for convenience
export NKI (Pos BinOp)

-- TODO: maybe change main instance?
scoped instance : BEq NKI.Fun where
  beq f1 f2 := f1.name == f2.name

/-
Terms are an extension of KLR.Expr, and they have types, which are an
extension of the KLR types. Notably, a Term can have type `obj Name`, which
represents an object type (a.k.a. a "nominal type").
Note: the implementation is currently abusing this type by using it for
functions. While this is not "incorrect," from the perspective of Python,
the goal is to eventually give all functions function types, and this
will happen once type inference is integrated.
-/
inductive TermType where
  | none | bool | int | float | string
  | obj    : Name -> TermType
  | tuple  : List TermType -> TermType
  | list   : List TermType -> TermType
  | tensor : Dtype -> Shape -> TermType
  deriving Repr, BEq

instance : Inhabited TermType where
  default := .obj "object".toName

/-
A term contains KLR expressions plus things that may exists at trace time.
References to modules, built-ins or user functions are only valid during
tracing. Also, none, strings, tuples and lists are only valid during tracing.
The ellipsis may be translated to a set of tensor indexes, or to a pass
statement depending on context. A slice is only valid in a tensor access
context in KLR, but may also be used with a list at trace time, or may float
around as a term for a while before it finds a home in a KLR term.

The store expression is an interesting case. In the original python
code, a store can show up in an expression context. For example:

  c = nl.load(a) + nl.load(b)

Which is technically:

  c = (store(t1, nl.load(a)) + store(t2, nl.load(b))

In KLR, these stores must be lifted up to the statement level:

  store(t1, nl.load(a))
  store(t2, nl.load(b))
  c = t1 + t2

The `store` term is an expression, and the tracing code will lift it
up to a KLR statement in the `RValue` function.

The tensor expression is a constant tensor that ephemerally appears during
tracing, then disappears after tracing eventually. An example is the output
of mgrid.

The mgrid expression is the 'mgrid' object in numpy and NKI. Its subscripted
form (with its indices) is represented using KLR.Python.Expr'.subscript .
-/
inductive Term where
  | module   : Name -> Term
  | builtin  : Name -> TermType -> Option Term -> Term
  | source   : NKI.Fun -> Term
  | none     : Term
  | string   : String -> Term
  | tuple    : List Term -> Term
  | list     : List Term -> Term
  | ellipsis : Term
  | slice    : Option Int -> Option Int -> Option Int -> Term
  | store    : Access -> Operator -> List Value -> Term
  | pointer  : Core.Address -> Term
  | expr     : Expr -> TermType -> Term
  | mgrid    : Term
  | mgItem   : Int -> Int -> Int -> Term
  deriving Repr, BEq

instance : Inhabited Term where
  default := .none

instance : Coe Bool Term where
  coe b := .expr (.value (.bool b)) .bool

instance : Coe Nat Term where
  coe i := .expr (.value (.int i)) .int

instance : Coe Int Term where
  coe i := .expr (.value (.int i)) .int

instance : Coe Float Term where
  coe f := .expr (.value (.float f)) .float

namespace Term

def nat (x : Nat) : Term := .expr (.value (.int x)) .int
def int (x : Int) : Term := .expr (.value (.int x)) .int
def float (x : Float) : Term := .expr (.value (.float x)) .float

-- Truthiness of Terms following Python

def isTrue : Term -> Err Bool
  | .none
  | .tuple []
  | .list []  => return false
  | .module _
  | .mgrid
  | .mgItem ..
  | .builtin ..
  | .source _
  | .string _
  | .tuple _
  | .list _
  | .ellipsis
  | .slice ..
  | .store ..
  | .pointer .. => return true
  | .expr (.value (.var _)) _ => return true
  | .expr (.value (.bool b)) _ => return b
  | .expr (.value (.int i)) _ => return i != 0
  | .expr (.value (.float f)) _ => return f != 0.0
  | .expr (.value (.access _)) _ => return true
  | .expr _ _ => throw "non-constant expression"

def isFalse (t : Term) : Err Bool :=
  return not (<- t.isTrue)


-- TODO: not efficient!
-- TODO: this is partial because of the use of flatMap
-- the ▷ syntax in Util could be updated to handle this case.
partial def tensor_list : Term -> List Core.TensorName
  | .module _ | .builtin .. | .source _ | .mgrid | .mgItem ..
  | .none | .string _
  | .ellipsis | .slice ..
  | .pointer .. => []
  | .tuple l | .list l => (l.flatMap tensor_list).eraseDups
  | .store a _ v => (tensors a ++ tensors v).eraseDups
  | .expr e _ => tensors e

instance : Tensors Term := ⟨ Term.tensor_list ⟩

end Term

/-
Our state has a number for generating fresh names, the current source location
(for error reporting), and the global and local environments. The set of fully
traced statements is held in the `body` field, and there is an array of
warnings which may be shown to the user after tracing.
-/

abbrev Env := Lean.RBMap Name Term compare

structure State where
  fvn : Nat := 0
  pos : Pos := { line := 0 }
  globals : Env := ∅
  locals : Env := ∅
  body : Array Stmt := #[]
  warnings : Array (Pos × String) := #[]
  tensorNames : Std.HashSet String := ∅
deriving Repr

instance : Inhabited State where
  default := {}

/-
Errors are introduced with `throw` either in the `Trace` monad or the `Err`
monad. The implementation of `throw` will create a `located` error. When we
reach a function boundary, the error is expanded into a `formatted` error
message.
-/
inductive TraceErr where
  | located : Pos -> String -> TraceErr
  | formatted : String -> TraceErr

instance : Inhabited TraceErr where
  default := .located { line := 0 } ""

abbrev Trace := EStateM TraceErr State

instance : MonadExcept String Trace where
  throw str := fun s => .error (.located s.pos str) s
  tryCatch m f := fun s =>
    match m s with
    | .ok x s => .ok x s
    | .error (.located _ str) s => f str s
    | .error (.formatted str) s => f str s

-- get the current source position
def getPos : Trace Pos := return (<- get).pos

-- modify the source position for `m`, reverting on exit
def withPos (p : Pos) (m : Trace a) : Trace a := fun s =>
  let p' := s.pos
  match m { s with pos := p } with
  | .ok x s => .ok x { s with pos := p' }
  | .error x s => .error x s

/-
Catch and report errors with source locations. The `withSrc` function is always
used a function boundaries, and converts `located` errors to `formatted`
errors.
-/
def withSrc (line : Nat) (source : String) (m : Trace a) : Trace a := fun s =>
  let p' := s.pos
  match m { s with pos := { line := 0 } } with
  | .ok x s => .ok x { s with pos := p' }
  | .error (.located p e) s =>
    .error (.formatted $ genError line source e p)
           { s with pos := p' }
  | .error (.formatted str) s =>
    .error (.formatted (str ++ genError line source "called from" s.pos))
           { s with pos := p' }
where
  genError (offset : Nat) (source err : String) (pos : Pos) : String :=
    let lines := source.splitOn "\n"
    let lineno := pos.line - 1
    let colno := pos.column
    let line := if h:lineno < lines.length
                then lines[lineno]'h
                else "<source not available>"
    let indent := (Nat.repeat (List.cons ' ') colno List.nil).asString
    s!"\nline {lineno + offset}:\n{line}\n{indent}^-- {err}"

-- generate a fresh name using an existing name as a prefix
def genName (name : Name := `tmp) : Trace Name :=
  modifyGet fun s =>
    let n := s.fvn + 1
    (.num name n, { s with fvn := n })

-- add a new binding to the global environment
def extend_global (x : Name) (v : Term) : Trace Unit :=
  modify fun s => {s with globals := s.globals.insert x v}

-- add a new binding to the local environment
def extend (x : Name) (v : Term) : Trace Unit :=
  modify fun s => {s with locals := s.locals.insert x v}

-- lookup a name in the global environment
def lookup_global? (name : Name) : Trace (Option Term) := do
  return (<- get).globals.find? name

-- lookup a name in the environment
def lookup? (name : Name) : Trace (Option Term) := do
  match (<- get).locals.find? name with
  | some t => return t
  | none => lookup_global? name

def lookup (name : Name) : Trace Term := do
  match <- lookup? name with
  | none => throw s!"name {name} not found"
  | some x => return x

-- Enter a new local scope, replacing the local environment on exit.
def enter (m : Trace a) : Trace a := fun s =>
  let locals := s.locals
  match m s with
  | .ok x s' => .ok x { s' with locals := locals }
  | .error err s => .error err s

-- Enter a new function scope, removing all local bindings
def enterFun (m : Trace a) : Trace a := fun s =>
  let locals := s.locals
  match m { s with locals := ∅ } with
  | .ok x s' => .ok x { s' with locals := locals }
  | .error err s => .error err s

-- append fully traced statement
def add_stmt (stmt : Pos -> Stmt) : Trace Unit :=
  modify fun s => { s with body := s.body.push (stmt s.pos) }

-- emit a warning
def warn (msg : String) : Trace Unit :=
  modify fun s => { s with warnings := s.warnings.push (s.pos, msg) }

-- check and register a tensor name
def checkTensorName (name : String) : Trace Unit := do
  let st <- get
  if st.tensorNames.contains name then
    throw s!"Tensor name '{name}' already in use"
  set { st with tensorNames := st.tensorNames.insert name }

-- generate a unique tensor name
def genTensorName : Trace String := do
  let st <- get
  let mut n := st.fvn -- arbitrary
  let mut name := ""
  repeat
    name := s!"tensor{n}"
    if not (st.tensorNames.contains name) then break
    n := n + 1
  set { st with tensorNames := st.tensorNames.insert name }
  return name

-- Either check or generate a tensor name
def tensorName : Option String -> Trace String
  | none => genTensorName
  | some n => do checkTensorName n; return n

-- Run a `Trace` monad computation, and handle any generated warnings or errors.
def tracer (g : List (Name × Term)) (m : Trace a) (showWarnings := true) : Err (String × a) :=
  match m { globals := Lean.RBMap.ofList g } with
  | .ok x s => .ok (addWarnings s "", x)
  | .error (.formatted str) s => .error (addWarnings s ("error:" ++ str))
  | .error (.located _ str) s => .error (addWarnings s ("error:" ++ str))
where
  addWarnings s str := if showWarnings then addWarn s str else str
  addWarn s str := s.warnings.foldl warnStr str
  warnStr str pw :=
    if pw.fst == { line := 0 } then
      s!"warning: {pw.snd}\n{str}"
    else
      s!"warning:{pw.fst.line}: {pw.snd}\n{str}"
