/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Util
import KLR.Core
import KLR.Python

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

-- Lean already has a perfectly nice hierarchical string type
export Lean (Name)
deriving instance Ord for Name

-- Bring in some Python types for convenience
export Python (Pos BoolOp CmpOp UnaryOp BinOp)

instance : BEq Python.Fun where
  beq f₁ f₂ := f₁.source == f₂.source

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
-/
inductive Term where
  | module   : Name -> Term
  | builtin  : Name -> TermType -> Term
  | source   : Python.Fun -> Term
  | none     : Term
  | string   : String -> Term
  | tuple    : List Term -> Term
  | list     : List Term -> Term
  | ellipsis : Term
  | slice    : Option Int -> Option Int -> Option Int -> Term
  | store    : Access -> Expr -> Term
  | expr     : Expr -> TermType -> Term
  deriving Repr, BEq

instance : Inhabited Term where
  default := .none

namespace Term

def type : Term -> TermType
  | .module name => .obj name
  | .builtin _ t => t
  | .source _    => .obj (.str .anonymous "function")
  | .none        => .none
  | .string _    => .string
  | .tuple l     => .tuple (types l)
  | .list l      => .list (types l)
  | .ellipsis    => .obj "ellipsis".toName
  | .slice _ _ _ => .obj "slice".toName
  | .store a _   => .tensor a.tensor.dtype a.shape
  | .expr _ t    => t
where
  types : List Term -> List TermType
  | [] => []
  | x :: xs => type x :: types xs

-- TODO not efficient!
mutual
partial def tensors : Term -> List Core.TensorName
  | .module _ => []
  | .builtin _ _ => []
  | .source _ => []
  | .none => []
  | .string _ => []
  | .tuple l | .list l => all_tensors l
  | .ellipsis    => []
  | .slice _ _ _ => []
  | .store a e   => (a.tensors ++ e.tensors).eraseDups
  | .expr e _    => e.tensors

partial def all_tensors (l : List Term) : List Core.TensorName :=
  (l.map tensors).flatten.eraseDups
end

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
  pos : Pos := { }
  globals : Env := ∅
  locals : Env := ∅
  body : Array Stmt := #[]
  warnings : Array (Pos × String) := #[]

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
  default := .located {} ""

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
  match m { s with pos := {} } with
  | .ok x s => .ok x { s with pos := p' }
  | .error (.located p e) s =>
    .error (.formatted $ Python.Parsing.genError line source e p)
           { s with pos := p' }
  | .error (.formatted str) s =>
    .error (.formatted (str ++ Python.Parsing.genError line source "called from" s.pos))
           { s with pos := p' }

-- generate a fresh name using an existing name as a prefix
def genName (name : Name := .anonymous) : Trace Name :=
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
def add_stmt (stmt : Stmt) : Trace Unit :=
  modify fun s => { s with body := s.body.push stmt }

-- emit a warning
def warn (msg : String) : Trace Unit :=
  modify fun s => { s with warnings := s.warnings.push (s.pos, msg) }

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
    if pw.fst == {} then
      s!"warning: {pw.snd}\n{str}"
    else
      s!"warning:{pw.fst.lineno}: {pw.snd}\n{str}"
