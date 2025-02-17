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

Tracing takes place within a pair of nested state monads called `TraceM` (the
inner one), and `Tracer` (the outer one). Most code only needs to use the
`TraceM` monad (more explanation of `Tracer`, and why we need it, is given later
in this file). The `TraceM` monad provides access to an environment which
contains bindings for all of the local variables currently in scope.

All local variables refer to `Term`s and hence may not be fully reduced. At the
completion of tracing, all terms must be reducible to `KLR.Expr`s or an error is
generated. This requirement is due to an implicit phase separation in the design
of NKI: some terms must be eliminated by tracing, and some terms can be passed
to the compiler. KLR only represents terms which can be passed on to the
compiler. For example, assertions have to be resolved at tracing time, neither
the compiler nor the hardware can raise an assertion that the user can see
during development. Hence, KLR does not have an assert statement, and any
expressions under an assert must be resolved during tracing. Other examples are
conditional expressions, and loop bounds; both of which must be resolved during
tracing.

In addition to `Term`s, the environment can contain built-in objects. Built-in
objects are defined using Lean functions that generate either other built-ins or
terms. For example, accessing an attribute of a built-in object may produce a
built-in function, which, when called, generates a KLR expression. There are
also built-ins at the `Tracer` monad level, which can generate KLR statements as
well as modify the environment of the `TraceM` monad.

This module defines types to represent the built-ins, the environments, and the
tracing monads.
-/

namespace KLR.Trace
open KLR.Core

-- Lean already has a perfectly nice hierarchical string type
export Lean (Name)
deriving instance Ord for Name

-- Bring in the operator types for convenience
export Python (BoolOp CmpOp UnaryOp BinOp)

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

mutual
/-
In python everything is an object, so we use the term "object" to refer to
all built-ins, be they objects, functions, constants, etc.
Each object has a name and a type, and may support up to four operations:
  - attr: attribute projection, e.g. obj.foo
  - access: subscript access, e.g. obj[1,2,3] or obj[1:2]
  - index: conversion to a tensor index, e.g. t[obj]
  - binop: apply binary operator, e.g. obj + 1
  - call: function call, e.g. f(a,b,k=1)
-/
structure Object where
  name   : Name
  type   : TermType := .obj name
  attr   : String -> Err Term
  access : List Index -> Err Term
  index  : TermType -> Nat -> Err Index
  binop  : Bool -> BinOp -> Expr -> Err Term
  call   : List Expr -> List (String × Expr) -> Err Term

/-
A term contains KLR expressions plus things that may exists at trace time.
Tuples and lists are only valid during tracing. The ellipsis may be translated
to a set of tensor indexes, or to a pass statement depending on context.
A slice is only valid in a tensor access context in KLR, but may also be
used with a list at trace time, or may float around as a term for a while
before it finds a home in a KLR term.

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
  | object   : Object -> Term
  | tuple    : List Term -> Term
  | list     : List Term -> Term
  | ellipsis : Term
  | slice    : Option Int -> Option Int -> Option Int -> Term
  | store    : TensorName -> List Index -> Expr -> Term
  | expr     : Expr -> TermType -> Term
end

instance : Inhabited Term where
  default := .expr (.const .none) .none

def Term.format : Term -> Lean.Format
  | .object obj => .text s!"object<{obj.name}>"
  | .tuple l => .text s!"tuple<{l.length}>"
  | .list l => .text s!"list<{l.length}>"
  | .ellipsis => .text "ellipsis"
  | .slice a b c => .text s!"slice({a},{b},{c})"
  | .store t ix e => repr (Stmt.store t ix e)
  | .expr e ty  => repr e ++ ":" ++ repr ty

instance : Repr Term where reprPrec b _ := b.format

def Term.beq : Term -> Term -> Bool
  | .object l, .object r => l.name == r.name
  | .tuple l , .tuple r
  | .list l  , .list r   => lst_eq l r
  | .ellipsis, .ellipsis => true
  | .slice a b c, .slice x y z => a == x && b == y && c == z
  | .expr l _, .expr r _ => l == r
  | _, _ => false
where
  lst_eq : List Term -> List Term -> Bool
  | [] , [] => true
  | l :: ls, r :: rs => Term.beq l r && lst_eq ls rs
  | _, _ => false

instance : BEq Term where beq := Term.beq

def Term.type : Term -> TermType
  | .object obj  => obj.type
  | .tuple l     => .tuple (types l)
  | .list l      => .list (types l)
  | .ellipsis    => .obj "ellipsis".toName
  | .slice _ _ _ => .obj "slice".toName
  | .store t _ _ => .tensor t.dtype t.shape -- TODO: incorrect, but unused?
  | .expr _ ty   => ty
where
  types : List Term -> List TermType
  | [] => []
  | x :: xs => type x :: types xs

def Term.toKLR : Term -> Err Core.Expr
  | .object obj  => return .var obj.name.toString
  | .tuple _     => throw "tuple cannot be converted to a KLR term"
  | .list _      => throw "list cannot be converted to a KLR term"
  | .ellipsis    => throw "ellipsis cannot be converted to a KLR term"
  | .slice _ _ _ => throw "slice cannot be converted to KLR in this context"
  | .store _ _ _ => throw "store cannot be converted to KLR in this context"
  | .expr e _    => return e

-- TODO not efficient!
mutual
partial def Term.tensors : Term -> List Core.TensorName
  | .object _  => []
  | .tuple l | .list l => all_tensors l
  | .ellipsis    => []
  | .slice _ _ _ => []
  | .store t _ _ => [t]
  | .expr e _    => e.tensors

partial def Term.all_tensors (l : List Term) : List Core.TensorName :=
  (l.map tensors).flatten.eraseDups
end

-- Our state has a number for generating fresh names, the current source
-- location (for error reporting), and the local environment. The global
-- environment is in the `Tracer` monad (below).

export KLR.Python (Pos)
abbrev Env := Lean.RBMap Name Term compare

structure State where
  fvn : Nat := 0
  pos : Pos := { }
  env : Env := ∅

namespace State

def ofList (l : List (String × Term)) : State :=
  { env := Lean.RBMap.ofList $ l.map fun (s,i) => (s.toName, i) }

def contains (s : State) (n : Name) : Bool :=
  s.env.contains n

end State

abbrev TraceM := StM State

-- Run a trace with an empty initial environment
def trace (m : TraceM a) : Err a :=
  match m.run { } with
  | .ok x _ => return x
  | .error s _ => throw s

-- generate a fresh name using an existing name as a prefix
def genName (name : Name := .anonymous) : TraceM Name := do
  let s <- get
  let n := s.fvn + 1
  set { s with fvn := n }
  return .num name n

-- add a new binding to the local environment
def extend (x : Name) (v : Term) : TraceM Unit :=
  modify fun s => {s with env := s.env.insert x v}

-- lookup a name in the local environment
def lookup? (name : Name) : TraceM (Option Term) := do
  let s <- get
  return s.env.find? name

def lookup (name : Name) : TraceM Term := do
  match (<- lookup? name) with
  | none => throw s!"local name {name} not found"
  | some x => return x


/-
The Tracer monad is setup similar to the TraceM monad, but "one level up".
Built-ins in Tracer can operate over Terms and within the TraceM monad, hence
they can query and modify the state of the inner monad.

The global environment contains module declarations, global objects, python
sources of user kernels, and possibly `Term`s. The global environment also
keeps the list of translated statements for the current kernel.

A module declaration is just a Name, like "nki", or "nki.isa". The tracing code
handles attributes of modules internally by extending the Name. For example,
reading the attribute "isa" of the module "nki", just produces a lookup of the
name "nki.isa", another module.

Global objects are similar to Objects, but operate over terms and can access
the TraceM monad. APIs, like "nki.language.arange", are implemented as Globals.
These implementations may produce Objects. Therefore, the set of Globals is
essentially fixed, and Objects can come and go as needed.

A source global is a user function which needs to be traced. When a function
call expression finds a source global, it kick starts the tracing process for
that user function.

Finally, a Term may appear in the global environment as a convient way to
represent global constants, such as `nki.language.psum`. Only the core tracing
code needs to use the `Tracer` monad.

Side note on why we can't combine TraceM and Tracer. The basic issue is
well-foundness. Essentially, our state monad is a function from state to
state and result `s -> (s,a)`. If we want our state to contain functions
that are in the monad (like Global.call below), we have to instantiate
s with `Collection (s -> (s,a))`. This is essentially Russell's paradox.
-/
structure Global where
  name : Name
  type : TermType := .obj name
  attr : String -> TraceM Term
  call : List Term -> List (String × Term) -> TraceM Term

inductive Item where
  | module : Name -> Item
  | global : Global -> Item
  | source : Python.Fun -> Item
  | term   : Term -> Item

def Item.type : Item -> TermType
  | .module n => .obj n
  | .global g => g.type
  | .source _ => .obj "source".toName
  | .term   t => t.type

def Item.toTerm : Item -> Err Term
  | .module n   => return .expr (.var n.toString) (.obj n)
  | .global g   => return .expr (.var g.name.toString) g.type
  | .source _   => throw "invalid use of source function"
  | .term t     => return t

structure Globals where
  env  : Lean.RBMap Name Item compare
  body : Array Stmt

-- The outer monad
abbrev Tracer := StateT Globals TraceM

def getState : Tracer State := (get : TraceM State)
def setState (s : State) : Tracer Unit := set s

def getPos : Tracer Pos :=
  fun g s => .ok (s.pos, g) s

def withPos (p : Pos) (m : Tracer a) : Tracer a :=
  fun g s => m g { s with pos := p }

def withSrc (line : Nat) (source : String) (m : Tracer a) : Tracer a :=
  try withPos {} m
  catch e => do
    let pos <- getPos
    throw (Python.Parsing.genError line source e pos)

/-
Enter a new scope, replacing the local state on exit. Note: we preserve the
position in the error case so the error handler (above) will get the
correct position on error. This should be fine since we are setting the
position on every statement and expression while traversing the tree.
-/

def enter (m : Tracer a) : Tracer a :=
  fun g s => match m g s with
  | .ok (x, g') _ => .ok (x, g') s
  | .error err s' => .error err { s with pos := s'.pos }

-- Enter a new function scope, removing all local bindings

def enterFun (m : Tracer a) : Tracer a :=
  enter $ do
    let s <- getState
    setState { s with env := ∅ }
    m

def extend_global (name : Name) (i : Item) : Tracer Unit :=
  modify fun s => { s with env := s.env.insert name i }

def lookup_global? (name : Name) : Tracer (Option Item) := do
  match (<- get).env.find? name with
  | none => return none
  | some x => return x

def lookup_global (name : Name) : Tracer Item := do
  match (<- get).env.find? name with
  | none => throw s!"global name {name} not found"
  | some x => return x

def lookup_item (name : Name) : Tracer Item := do
  match (<- lookup? name) with
  | some x => return .term x
  | none => lookup_global name

def add_stmt (s : Stmt) : Tracer Unit :=
  modify fun g => { g with body := g.body.push s }

def tracer (g : Globals) (m : Tracer a) : Err a :=
  match trace (m.run g) with
  | .ok x => .ok x.fst
  | .error s => .error s
