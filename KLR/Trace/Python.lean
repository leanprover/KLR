/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Core
import KLR.Python
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Basic

namespace KLR.Trace
open KLR.Python
open Core (tensors)

def const : Const -> Term
  | .none     => .none
  | .bool b   => .expr (.value $ .bool b)   .bool
  | .int i    => .expr (.value $ .int i)    .int
  | .float f  => .expr (.value $ .float f)  .float
  | .string s => .string s
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

-- Convert a Term to an Index (if possible)
def termToIndex (shape : Core.Shape) : Term -> Err (List Core.Index)
  | .tuple l | .list l => toIndex shape l
  | t => toIndex shape [t]
where
  slice (d : Nat) := Core.Index.slice (some 0) (some (Int.ofNat d)) (some 1)
  toIndex : Core.Shape -> List Term -> Err (List Core.Index)
  | [], []
  | [], [.ellipsis] => return []
  | [], _  => throw "too many indexes for shape"
  | ds, [] => return ds.map slice
  | d :: ds, t :: ts =>
    match t with
    | .none => return slice d :: (<- toIndex ds ts)
    | .ellipsis =>
        if ds.length + 1 == ts.length
        then toIndex (d::ds) ts
        else return slice d :: (<- toIndex ds (t::ts))
    | .slice x y z => do
        let d := Int.ofNat d
        let x := x.getD 0
        let y := y.getD d
        let z := z.getD 1
        if x < 0 || x >= d || y < 0 || y > d || z <= 0 then
          throw "index out of range of tensor dimension"
        return .slice x y z :: (<- toIndex ds ts)
    | .tuple _ | .list  _ => throw "nested tuple/list indexes not supported"
    | t => do
        let i : Int <- fromNKI? t
        if i < 0 || i >= d then
          throw "index out of range of tensor dimension"
        return .coord i :: (<- toIndex ds ts)

-- Note, a list index can be negative, which means index from end of list.
-- Python also allows l[True] and l[False]
-- TODO: add case for slice
def list_access (name : String) (l : List Term) : Term -> Err Term
  | .expr (.value (.bool false)) _ => do
      if h:l.length > 0 then return l.get (Fin.mk 0 h)
      else throw "index out of bounds"
  | .expr (.value (.bool true)) _ => do
      if h:l.length > 1 then return l.get (Fin.mk 1 h)
      else throw "index out of bounds"
  | .expr (.value (.int i)) _ => do
      let i := if i < 0 then l.length + i else i
      if i < 0 then throw "index out of bounds"
      let n := i.toNat
      if h:l.length > n then return l.get (Fin.mk n h)
      else throw "index out of bounds"
  |_ => throw s!"{name} indicies must be integers of slices"

-- Top-level subscript access t[i]
-- TODO: add case for String
def access (t : Term) (i : Term) : Err Term := do
  match t with
  | .module _
  | .builtin ..
  | .source _
  | .none
  | .ellipsis
  | .slice ..
  | .store .. => throw "subscript not supported"
  | .string _ => throw "string subscript not implemented"
  | .tuple l => list_access "list" l i
  | .list l => list_access "tuple" l i
  | .expr .. => do
      let tensor : Core.TensorName <- fromNKI? t
      let access := Core.Access.basic tensor (<- termToIndex tensor.shape i)
      let shape <- Tensor.inferShape access
      return .expr (.value (.access access)) (.tensor tensor.dtype shape)

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
def LValue : Expr -> Trace Term
  | .exprPos e' p => withPos p (lval e')
where
  lval : Expr' -> Trace Term
  | .name id .store => return .expr (.value $ .var id) (.obj "object".toName)
  | .attr _ id .store => throw s!"cannot assign to attribute {id}"
  | .tuple l .store => return .tuple (<- LValue ▷ l)
  | .list  l .store => return .list  (<- LValue ▷ l)
  | .subscript _ _ .store => throw "unimp subscript store"
  | _ => throw "cannot assign to expression"

-- Convert an R-Value to a pure expression, emitting
-- additional assignments as needed.
def RValue : Term -> Trace Term
  | .module n => return .module n
  | .builtin n t => return .builtin n t
  | .source f => return .source f
  | .none => return .none
  | .string s => return .string s
  | .tuple  l => return .tuple (<- RValue ▷ l)
  | .list   l => return .list  (<- RValue ▷ l)
  | .ellipsis => return .ellipsis
  | .slice a b c => return .slice a b c
  | .store acc op args => do
       add_stmt (.store acc op args)
       let shape <- Tensor.inferShape acc
       return .expr (.value (.access acc)) (.tensor acc.tensor.dtype shape)
  | .expr e@(.call ..) ty => do
       let v := (<- genName).toString
       add_stmt (.assign v e)
       return .expr (.value $ .var v) ty
  | .expr e ty => return .expr e ty

-- Create an assignment to a Core Expr, this must be a variable
def assignExpr (e : Core.Expr) (t : Term) : Trace Unit := do
  match e with
  | .value (.var x) => extend x.toName t
  | _ => throw s!"cannot assign to {repr e}"

-- Unpack an RValue, must be a list or tuple
def unpack : Term -> Trace (List Term)
  | .tuple l | .list  l => return l
  | t => throw s!"cannot unpack non-iterable object {repr t}"

-- Assign to a term, handling unpacking for tuples and lists
def assignTerm (x : Term) (e : Term) : Trace Unit := do
  match x with
  | .module name => throw s!"cannot assign to {name}"
  | .builtin name _ => throw s!"cannot assign to {name}"
  | .source _ => throw "cannot assign to function"
  | .none => throw "cannot assign to None"
  | .string _ => throw "cannot assign to a string literal"
  | .tuple l
  | .list  l  => assignList l (<- unpack e)
  | .ellipsis => throw "cannot assign to ellipsis"
  | .slice .. => throw "cannot assign to slice"
  | .store .. => throw "cannot assign to a store"
  | .expr x _ => assignExpr x e
where
  assignList : List Term -> List Term -> Trace Unit
  | [], [] => return ()
  | [], _  => throw "not enough values to unpack"
  | _, []  => throw "too many values to unpack"
  | x::xs, t::ts => do
      assignTerm x t;
      assignList xs ts

-- Top-level assignment handling
-- e.g. x1 = x2 = e
def assign (xs : List Expr) (e : Term) : Trace Unit := do
  let xs <- LValue ▷ xs
  let e <- RValue e
  for x in xs do
    assignTerm x e

-- Translation of for-loop iterators

-- range, but only in a for-loop context
private def range (start stop step : Int) : List Term :=
  let int i := Term.expr (.value (.int i)) .int
  if step = 0 then []
  else if 0 < step then
    if stop <= start then [] else
    if stop <= start + step then [int start] else
    int start :: range (start + step) stop step
  else -- step < 0
    if start <= stop then [] else
    if start + step <= stop then [int start] else
    int start :: range (start + step) stop step
termination_by (stop - start).natAbs

def termToIter : Term -> Err (List Term)
  | .tuple l | .list l => return l
  | .expr (.call "range" l _) _ =>
       match l with
       | [ .int e ] => return (range 0 e 1)
       | [ .int s, .int e ] => return (range s e 1)
       | [ .int s, .int e, .int t ] =>
           if t == 0
           then throw "range arg 3 must not be zero"
           else return (range s e t)
       | _ => throw "invalid argument to range"
  | _ => throw "unsupported loop interator"

/-
# Expressions and Statements
-/

-- return type of statement evaluator (see stmt below)
inductive StmtResult where
  | done | brk | cont | ret (t : Term)
  deriving Repr, BEq

mutual

partial def expr [FromNKI a] : Expr -> Trace a
  | .exprPos e' p => withPos p do fromNKI? (<- expr' e')

-- This is only used for slices
partial def integer? : Option Expr -> Trace (Option Int)
  | none => return none
  | some e => expr e

partial def expr' : Expr' -> Trace Term
  | .const c => return const c
  | .tensor s dty => do
      let shape <- expr ▷ s
      let name <- genName "t".toName
      let dty <- fromNKI? (.expr (.value $ .var dty) .none)
      return .expr (.value $ .access $ .simple ⟨ name.toString, dty, shape, .dram ⟩) (.tensor dty shape)
  | .name id _ => lookup id.toName
  | .attr e id _ => do ((<- expr e : Term).attr id)
  | .tuple l _ => return .tuple (<- expr ▷ l)
  | .list  l _ => return .list  (<- expr ▷ l)
  | .subscript t i _ => do access (<- expr t) (<- expr i)
  | .slice x y z => return .slice (<- integer? x) (<- integer? y) (<- integer? z)
  | .boolOp op xs => do boolOp op (<- expr ▷ xs)
  | .binOp op l r => do binOp op (<- expr l) (<- expr r)
  | .unaryOp op e => do unOp op (<- expr e)
  | .compare l ops cs => do compare (<- expr l) ops (<- expr ▷ cs)
  | .ifExp tst tru fls => do
      let tst <- (<- expr tst : Term).isTrue
      let tru <- expr tru  -- eagerly evaluate both branches
      let fls <- expr fls  -- to report errors to user
      return if tst then tru else fls
  | .call f args kws => do
      match (<- expr f : Term) with
      | .builtin n _ => do (<- builtinFn n) (<- expr ▷ args) (<- keyword expr ▷ kws)
      | .source f    => do function_call f (<- expr ▷ args) (<- keyword expr ▷ kws)
      | .expr (.value (.var f)) _ =>
          return .expr (.call f (<- expr ▷ args) (<- keyword expr ▷ kws)) default
      | _ => throw "not a callable type"

partial def keyword (f : Expr -> Trace a) : Keyword -> Trace (String × a)
  | .keyword id e p => withPos p do return (id, (<- f e))

partial def stmt : Stmt -> Trace StmtResult
  | .stmtPos s' p => withPos p (stmt' s')

partial def stmt' : Stmt' -> Trace StmtResult
  | .pass => return .done
  | .ret e => do
      let t <- expr e
      let t <- RValue t
      return .ret t
  | .expr e => do
      let t <- expr e
      let _ <- RValue t
      return .done
  | .assert e => do
      let t : Term <- expr e
      if (<- t.isFalse) then throw "assertion failed"
      return .done
  | .assign xs e => do assign xs (<- expr e); return .done
  | .augAssign x op e => do assign [x] (<- expr' (.binOp op x e)); return .done
  | .annAssign _ _ .none => return .done
  | .annAssign x _ (.some e) => do assign [x] (<- expr e); return .done
  | .ifStm e thn els => do
      let t : Term <- expr e
      let body := if <- t.isTrue then thn else els
      stmts body
  | .forLoop x iter body orelse => do
      let x <- LValue x
      let iter <- expr iter
      let ts <- termToIter iter
      for t in ts do
        assignTerm x t
        let res <- stmts body
        if res == .cont then continue
        if res == .brk then break
        if let .ret _ := res then return res
      stmts orelse
  | .breakLoop => return .brk
  | .continueLoop => return .cont

partial def stmts : List Stmt -> Trace StmtResult
  | [] => return .done
  | s :: l => do
      match <- stmt s with
      | .done => stmts l
      | r => return r

-- Bind positional and keyword arguments to a Python function based on its
-- signature.

partial def bind_args (f : Fun)
                      (args : List Term)
                      (kwargs : List (String × Term))
                      (rename : Bool := false)
                      : Trace (List (String × Term)) := do
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
      return (x, <- expr' e)
    else
      throw s!"argument {x} not supplied"
  -- rename tensors if asked to
  let argmap := if rename then argmap.map renameTensors else argmap
  return argmap
where
  renameTensors : String × Term -> String × Term
  | (s, .expr (.value (.access a)) ty) => (s, .expr (.value (.access (renameAcc s a))) ty)
  | other => other
  renameAcc (s : String) : Core.Access -> Core.Access
  | .simple t => .simple (renameTN s t)
  | .basic t l => .basic (renameTN s t) l
  | .pattern t o l => .pattern (renameTN s t) o l
  renameTN (s : String) (t : Core.TensorName) : Core.TensorName := { t with name := s }

/-
Function calls are split into two parts because we need to handle the top-level
kernel function differently: its argument tensors will be inputs, but internal
function call arguments will not be input tensors.
-/
partial def call (f : Fun)
                 (args : List (String × Term))
                 : Trace Term := do
  withSrc f.line f.source $ enterFun $ do
    args.forM fun (x,e) => do extend x.toName e
    match <- stmts f.body with
    | .ret t => return t
    | _ => return .none

partial def function_call (f : Fun)
                          (args : List Term)
                          (kwargs : List (String × Term))
                          : Trace Term := do
  let args <- bind_args f args kwargs (rename:=false)
  call f args

end

/-
Evaluate each global in the current environment, skipping any globals that are
already defined. We do not redefine globals, because we may have picked up
functions with dummy implementations, e.g., nki.language.add is defined as:

  def add(x,y): pass

in the official NKI API. We do not want this to shadow the built-in definition
of add, if we have one. If we have an internal definition, we will use this
over anything found during parsing.
-/
private def globals (k : Kernel) : Trace Unit := do
  let s <- get
  for (n, f) in k.funcs do
    let n := n.toName
    if not (s.globals.contains n) then
      extend_global n (.source f)
  for (n,e) in k.globals do
    let name := n.toName
    if not (s.globals.contains name) then
      if not (k.undefinedSymbols.contains n) then
        extend_global name (<- expr' e)

/-
Check all of the undefined names against the global environment. If an
undefined name has a builtin implementation, then it is OK. In
addition, we allow undefined names in certain special modules. This is
because, for certain modules, we want to pass anything we don't know
about through to KLR. For example, if NKI creates a new experimental
api `nki.isa.newfn`, then rather than generating an error, a call to
this function will end up in the KLR:

  x[...] = nki.isa.newfn(t, 3)

  .store (.access x ...)
    .call (.var "nki.isa.newfn") [t, .const 3] ...

Of course, the compiler will then fail, not knowing how to translate
this constant. However, you still get out a KLR artifact that some
other, experimental compiler may be able to handle.
-/
def undefinedOK : Name -> Bool
  | .str .anonymous "nki" => true
  | .str n _ => undefinedOK n
  | _ => false

def checkUndefined (k : Kernel) : Trace Unit := do
  let mut undefined := []
  for sym in k.undefinedSymbols do
    let name := sym.toName
    if (<- lookup_global? name).isNone then
      if undefinedOK name then do
        warn s!"unknown NKI API {name}"
        extend_global name (.expr (.value $ .var name.toString) (.obj name))
      else
        undefined := name :: undefined
  if undefined.length > 0 then
    throw s!"undefined names {undefined}"

-- Call the top-level kernel function
def traceKernel (k : Kernel) : Trace Core.Kernel := do
  globals k
  checkUndefined k
  match k.funcs.lookup k.entry with
  | none => throw s!"function {k.entry} not found"
  | some f => do
      let args <- k.args.mapM expr'
      let kwargs <- k.kwargs.mapM fun (x,e) => return (x, <- expr' e)
      let args <- bind_args f args kwargs (rename := true)
      let res <- call f args
      let inputs := tensors (args.map fun x => x.snd)
      let outputs := tensors res
      return {
        name := k.entry
        inputs := inputs
        outputs := outputs
        body := (<- get).body.toList
      }

def PythonEnv :=
  let const s := Builtin.const_var (.str .anonymous s)
  [
    const "range"
  ]
