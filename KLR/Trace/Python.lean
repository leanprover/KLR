/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Core
import KLR.Python
import KLR.Trace.Types
import KLR.Trace.Basic

namespace KLR.Trace
open KLR.Python

def const : Const -> Term
  | .none     => .expr (.const $ .none)     .none
  | .bool b   => .expr (.const $ .bool b)   .bool
  | .int i    => .expr (.const $ .int i)    .int
  | .float f  => .expr (.const $ .float f)  .float
  | .string s => .expr (.const $ .string s) .string
  | .ellipsis => .ellipsis

/-
# Evaluating index expressions

An index expression occurs only within a subscript expression. For example, in
the expression:

  t[1,1:10,None,x+9]

all of 1, 1:10, None, and x+9 are indexes. Note None may also be written as
np.newaxis. Also, a None or a slice (or ellipsis) may only occur at the
outer-most level of an index: if you write, e.g.

  t[x+None]

then the None is interpreted as an integer and not as a new axis. If you write,

  t[(1:2) + 3]
  t[... * 8]

these are syntax errors in python. Note, we do not support nested tuples or
lists as indexes e.g. t[1,(2,3),4] is disallowed
-/

-- Convert an Expr to an Index (if possible)
def exprToIndex : Core.Expr -> Err Core.Index
  | .var x => return .coord (some $ .var x)
  | .const .none => return .coord none
  | .const c => return .coord (some $ .int (<- c.toInt))
  | .tensor _ => throw "tensor indirect indexing unsupported"
  | .access _ _ => throw "invalid index"
  | .operator _ => throw "invalid index"
  | .call _ _ _ => throw "invalid index"

-- Convert a Term to an Index (if possible)
def termToIndex (ty : TermType) : Term -> Err (List Core.Index)
  | .tuple l | .list l => l.enum.mapM fun (p,t) => toIndex p t
  | t => return [<- toIndex 0 t]
where
  toIndex (pos : Nat) : Term -> Err Core.Index
  | .tuple _ | .list  _ => throw "nested tuple/list indexes not supported"
  | .object o => o.index ty pos
  | .ellipsis => return .ellipsis
  | .slice x y z => return .slice (x.map .int) (y.map .int) (z.map .int)
  | .store _ _ _ => throw "store expression cannot be used as index"
  | .expr e _ => exprToIndex e

-- Note, a list index can be negative, which means index from end of list.
-- Python also allows l[True] and l[False]
-- TODO: add case for slice
def list_access (name : String) (l : List Term) : Term -> Err Term
  | .expr (.const (.bool false)) _ => do
      if h:l.length > 0 then return l.get (Fin.mk 0 h)
      else throw "index out of bounds"
  | .expr (.const (.bool true)) _ => do
      if h:l.length > 1 then return l.get (Fin.mk 1 h)
      else throw "index out of bounds"
  | .expr (.const (.int i)) _ => do
      let i := if i < 0 then l.length + i else i
      if i < 0 then throw "index out of bounds"
      let n := i.toNat
      if h:l.length > n then return l.get (Fin.mk n h)
      else throw "index out of bounds"
  |_ => throw s!"{name} indicies must be integers of slices"

-- Top-level subscript access t[i]
def access (t : Term) (i : Term) : Err Term := do
  match t with
  | .object o => o.access (<- termToIndex t.type i)
  | .tuple l => list_access "list" l i
  | .list l => list_access "tuple" l i
  | .ellipsis
  | .slice _ _ _ => throw "__subscript__ not supported"
  | .store _ _ _ => throw "__subscript__ not supported"
  | .expr e _ => return .expr (.access e (<- termToIndex t.type i)) (.obj "object".toName)

/-
# Handling of assignment statements

Assignments can be things like:

  x = y = 1
  a, y = (1,2)

or even

  (x,y), z = a, [b,c] = f()

The current implementation requires that these kinds of complex assignments are
expanded at tracing time. That is, in the example above the call to f must
generate a tuple or list of the right size at tracing time. This will then be
expanded out to assignments of the individual variables.

In general, we need to make sure the right-hand side is only evaluated once. For
example, consider the assignment below:

  (x,y) = a = (f(), 1)

The following is and incorrect translation, because f is called twice.

  a = (f(), 1)
  x = f()  # INCORRECT
  y = 1

One correct translation is:

  tmp = f()
  a = (tmp, 1)
  x = tmp
  y = 1

The extra variable `tmp` is only needed if the right-hand side has side-effects
or is expensive to compute. Otherwise, it is safe to copy the right-hand side
everywhere it is needed.

In the above case, only the first assignment is emitted to the translated
function. The other three assignments are placed in the environment, but not
emitted. Therefore any uses of a, x, or y will be replaced with their
assignments. This is effectively a simple form of constant propagation and
dead-code elimination for simple assignments.
-/

-- Convert an expression in assignment context (an L-Value).
-- TODO: handle subscript
def LValue : Expr -> Tracer Term
  | .exprPos e' p => withPos p (lval e')
where
  lval : Expr' -> Tracer Term
  | .name id .store => return .expr (.var id) (.obj "object".toName)
  | .attr _ id .store => throw s!"cannot assign to attribute {id}"
  | .tuple l .store => return .tuple (<- LValue ▷ l)
  | .list  l .store => return .list  (<- LValue ▷ l)
  | .subscript _ _ .store => throw "unimp subscript store"
  | _ => throw "cannot assign to expression"

-- Convert an R-Value to a pure expression, emitting
-- additional assignments as needed.
def RValue : Term -> Tracer Term
  | .object o => return .object o
  | .tuple  l => return .tuple (<- RValue ▷ l)
  | .list   l => return .list  (<- RValue ▷ l)
  | .ellipsis => return .ellipsis
  | .slice a b c => return .slice a b c
  | .store t ix e => do
       add_stmt (.store t ix e)
       if ix == []
       then return .expr (.tensor t) (.tensor t.dtype t.shape)
       else return .expr (.access (.tensor t) ix) (.tensor t.dtype t.shape)
  | .expr e@(.call _ _ _) ty => do
       let v := (<- genName).toString
       add_stmt (.assign v e)
       return .expr (.var v) ty
  | .expr e ty => return .expr e ty

-- Create an assignment to a Core Expr, this must be a variable
def assignExpr (e : Core.Expr) (t : Term) : Tracer Unit := do
  match e with
  | .var x => extend x.toName t
  | _ => throw s!"cannot assign to {repr e}"

-- Unpack an RValue, must be a list or tuple
def unpack : Term -> Tracer (List Term)
  | .tuple l | .list  l => return l
  | t => throw s!"cannot unpack non-iterable object {repr t}"

-- Assign to a term, handling unpacking for tuples and lists
def assignTerm (x : Term) (e : Term) : Tracer Unit := do
  match x with
  | .object o => throw s!"cannot assign to {o.name}"
  | .tuple l
  | .list  l  => assignList l (<- unpack e)
  | .ellipsis => throw "cannot assign to ellipsis"
  | .slice _ _ _ => throw "cannot assign to slice"
  | .store _ _ _ => throw "cannot assign to a store"
  | .expr x _ => assignExpr x e
where
  assignList : List Term -> List Term -> Tracer Unit
  | [], [] => return ()
  | [], _  => throw "not enough values to unpack"
  | _, []  => throw "too many values to unpack"
  | x::xs, t::ts => do
      assignTerm x t;
      assignList xs ts

-- Top-level assignment handling
-- e.g. x1 = x2 = e
def assign (xs : List Expr) (e : Term) : Tracer Unit := do
  let xs <- LValue ▷ xs
  let e <- RValue e
  for x in xs do
    assignTerm x e

/-
# Expressions and Statements
-/

mutual
partial def expr : Expr -> Tracer Item
  | .exprPos e' p => withPos p (expr' e')

partial def term (e : Expr) : Tracer Term :=
  return <- (<- expr e).toTerm

partial def term' (e : Expr') : Tracer Term :=
  return <- (<- expr' e).toTerm

partial def klr (e : Expr) : Tracer Core.Expr :=
  return <- (<- term e).toKLR

partial def nat (e : Expr) : Tracer Nat := do
  match <- klr e with
  | .const c => return (<- c.toInt).toNat
  | _ => throw "expecting positive integer"

-- Note, this is technically more permissive than python in some contexts (slices)
partial def integer? : Option Expr -> Tracer (Option Int)
  | none => return none
  | some e => do
    match <- klr e with
    | .const .none => return none
    | .const c => return some (<- c.toInt)
    | _ => throw "expecting integer or None"

partial def expr' : Expr' -> Tracer Item
  | .const c => return .term (const c)
  | .tensor s dty => do
      let shape <- nat ▷ s
      let name <- genName "t".toName
      return .term (.expr (.tensor ⟨ name.toString, dty, shape, .dram ⟩) (.tensor dty shape))
  | .name id _ => lookup_item id.toName
  | .attr (.exprPos e p) id _ => do withPos p ((<- expr' e).attr id)
  | .tuple l _ => return .term (.tuple (<- term ▷ l))
  | .list  l _ => return .term (.list  (<- term ▷ l))
  | .subscript t i _ => return .term (<- access (<- term t) (<- term i))
  | .slice x y z => return .term (.slice (<- integer? x) (<- integer? y) (<- integer? z))
  | .boolOp op xs => return .term (<- boolOp op (<- term ▷ xs))
  | .binOp op l r => return .term (<- binOp op (<- term l) (<- term r))
  | .unaryOp op e => return .term (<- unOp op (<- term e))
  | .compare l ops cs => return .term (<- compare (<- term l) ops (<- term ▷ cs))
  | .ifExp tst tru fls => do
      let tst <- (<- term tst).isTrue
      let tru <- expr tru  -- eagerly evaluate both branches
      let fls <- expr fls  -- to report errors to user
      return if tst then tru else fls
  | .call f args kws => do
      match <- expr f with
      | .module n => throw s!"module {n} not callable"
      | .global g => return .term (<- g.call (<- term ▷ args) (<- keyword term ▷ kws))
      | .term t   => return .term (<- t.call (<- klr ▷ args) (<- keyword klr ▷ kws))
      | .source f => return .term (<- function_call f (<- term ▷ args) (<- keyword term ▷ kws))

partial def keyword (f : Expr -> Tracer a) : Keyword -> Tracer (String × a)
  | .keyword id e p => withPos p do return (id, (<- f e))

partial def stmt : Stmt -> Tracer (Option Term)
  | .stmtPos s' p => withPos p (stmt' s')

partial def stmt' : Stmt' -> Tracer (Option Term)
  | .pass => return none
  | .ret e => do
      let t <- term e
      let t <- RValue t
      return some t
  | .expr e => do
      let t <- term e
      let _ <- RValue t
      return none
  | .assert e => do
      let t <- term e
      if (<- t.isFalse) then throw "assertion failed"
      return none
  | .assign xs e => do assign xs (<- term e); return none
  | .augAssign x op e => do assign [x] (<- term' (.binOp op x e)); return none
  | .annAssign _ _ .none => return none
  | .annAssign x _ (.some e) => do assign [x] (<- term e); return none
  | _s => throw "not yet implemented"

partial def stmts : List Stmt -> Tracer Term
  | [] => return .expr (.const .none) .none
  | s :: l => do
      match <- stmt s with
      | none => stmts l
      | some t => return t

-- Bind positional and keyword arguments to a Python function based on its
-- signature.

partial def bind_args (f : Fun)
                      (args : List Term)
                      (kwargs : List (String × Term))
                      (rename : Bool := false)
                      : Tracer (List (String × Term)) := do
  if f.args.vararg != none || f.args.kwarg != none then
    throw "var args not supported"
  if args.length < f.args.posonlyargs.length then
    throw "not enough arguments"
  let dflts := f.args.all_defaults
  let names := f.args.names
  if args.length + kwargs.length > names.length then
    throw "too many arguments supplied (varargs not supported)"
  let argmap <- f.args.names.enum.mapM fun (i,x) => do
    if h:args.length > i then
      return (x, args.get (Fin.mk i h))
    else if let some v := kwargs.lookup x then
      return (x, v)
    else if let some e := dflts.lookup x then
      return (x, <- term' e)
    else
      throw s!"argument {x} not supplied"
  -- rename tensors if asked to
  let argmap := if rename then argmap.map renameTensors else argmap
  return argmap
where
  renameTensors : String × Term -> String × Term
  | (s, .expr (.tensor t) ty) => (s, .expr (.tensor {t with name := s}) ty)
  | other => other

/-
Function calls are split into two parts because we need to handle the top-level
kernel function differently: its argument tensors will be inputs, but internal
function call arguments will not be input tensors.
-/
partial def call (f : Fun)
                 (args : List (String × Term))
                 : Tracer Term := do
  withSrc f.line f.source $ enterFun $ do
    args.forM fun (x,e) => do extend x.toName e
    stmts f.body

partial def function_call (f : Fun)
                          (args : List Term)
                          (kwargs : List (String × Term))
                          : Tracer Term := do
  let args <- bind_args f args kwargs (rename:=false)
  call f args

end

/-
Evaluate each global in the current environment, skipping any globals that are
already defined. We do not redefine globals because, we may have picked up
functions with dummy implementations, e.g., nki.language.add is defined as:

  def add(x,y): pass

in some versions of the code. We do not want this to shadow a built-in
definition of add. If we have an internal definition, we will use this over
anything found during parsing.
-/

private def globals (k : Kernel) : Tracer Unit := do
  let s <- get
  for (n, f) in k.funcs do
    let n := n.toName
    if not (s.env.contains n) then
      extend_global n (.source f)
  for (n,e) in k.globals do
    let n := n.toName
    if not (s.env.contains n) then
      extend_global n (<- expr' e)

-- Call the top-level kernel function
def traceKernel (k : Kernel) : Tracer Core.Kernel := do
  globals k
  match k.funcs.lookup k.entry with
  | none => throw s!"function {k.entry} not found"
  | some f => do
      let args <- k.args.mapM term'
      let kwargs <- k.kwargs.mapM fun (x,e) => return (x, <- term' e)
      let args <- bind_args f args kwargs (rename := true)
      let res <- call f args
      let inputs := Term.all_tensors (args.map fun x => x.snd)
      let outputs := Term.tensors res
      return {
        name := k.entry
        inputs := inputs
        outputs := outputs
        body := (<- get).body.toList
      }

def runKernel (k : Kernel) : Err Core.Kernel :=
  tracer ⟨ ∅, #[] ⟩ (traceKernel k)
