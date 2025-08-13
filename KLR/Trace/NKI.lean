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
import KLR.NKI.Basic
import KLR.Trace.Builtin
import KLR.Trace.ISA
import KLR.Trace.Term
import KLR.Trace.Types

/-
# NKI built-ins

This module defines the builtin constants used by tracing for NKI kernels.
-/
namespace KLR.Trace
open KLR.NKI

private def neuronxcc : Name := .str .anonymous "neuronxcc"
private def nki_ : Name := .str neuronxcc "nki"
private def nki_isa : Name := .str nki_ "isa"
private def nki_lang : Name := .str nki_ "language"
private def nisa_cmd : Name := .str nki_isa "reduce_cmd"

private def nl : String -> Name := .str nki_lang
private def nisa : String -> Name := .str nki_isa

-- NKI environment, including constants and the names of builtin functions
-- TODO: these should be defined in Python, not here
def NKIEnv : List (Name × Term) :=
  [ module neuronxcc
  , module nki_
  , module nki_isa
  , module nki_lang
  , module nisa_cmd
  , const_int (.str (nl "tile_size") "pmax") 128
  , const_int (.str (nl "tile_size") "gemm_stationary_fmax") 128
  , const_int (.str (nl "tile_size") "gemm_moving_fmax") 512
  , const_int (.str (nisa "nc_version") "gen1") 1
  , const_int (.str (nisa "nc_version") "gen2") 2
  , const_int (.str (nisa "nc_version") "gen3") 3
  , (nl "mgrid", .mgrid)
  ]
  ++ builtinEnv.map fun (x,_) => (x, .builtin x (.obj x) none)


-- The result of a statement evaluation
inductive Result where
  | next | brk | cont | ret (t : Term)
  deriving Repr, BEq

-- Bind arguments to a Python function based on its signature.
-- See also: Simplify.lean which checks for varargs signatures
def bindArgs (f : Fun)
             (args : List Expr)
             (kwargs : List Keyword)
             : Trace (List Keyword) := do
  if args.length + kwargs.length > f.args.length then
    warn "extra arguments ignored (varargs not supported)"
  f.args.zipIdx.mapM fun ({name := x, dflt := d}, i) => do
    if h:args.length > i then
      pure ⟨x, args.get (Fin.mk i h)⟩
    else if let some kw := kwargs.find? fun kw => kw.name == x then
      pure kw
    else if let some e := d then
      pure ⟨x, e⟩
    else
      throw s!"argument {x} not supplied"

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

-- Lookup a name, falling back to attribute if not found
private def lookupName (name : Name) : Trace Term := do
  match <- lookup? name with
  | some t => return t
  | none =>
    match name with
    | .str .anonymous _ => throw "error: empty name"
    | .str n id => (<- lookupName n).attr id
    | _ => throw s!"{name} not found"

/-
Best effort checks for slice overflow

Currently this implementation will silently clip out-of-bounds slice patterns,
similar to Python and numpy. However, to aide developers we will (try to) warn
or fail if we detect an overflow. This function is applied to function
arguments.
-/
private def checkAccess (t : Term) (warnOnly : Bool := true) : Trace Unit := do
  match t with
  | .expr (.value (.access (.basic b))) _ => do
    let shape <- b.shape
    for (dim, ndx) in shape.toList.zip b.indexes do
      if dim < ndx.size then
        if warnOnly then warn "index overflow"
        else throw "inddex overflow"
  | _ => return ()

-- Values

def value : Value -> Trace Term
  | .none      => return .none
  | .bool b    => return .expr (.value $ .bool b)   .bool
  | .int i     => return .expr (.value $ .int i)    .int
  | .float f   => return .expr (.value $ .float f)  .float
  | .string s  => return .string s
  | .tensor s dty (some name) => do
      let shape <- Core.Shape.fromList s
      let dtype <- fromNKI? (.expr (.value $ .var dty) .none)
      let addr : Core.Address := {
        memory := .hbm
        parSize := shape.parDim
        freeSize := shape.freeElements * dtype.size
      }
      let tensor <- Core.TensorName.make name dtype shape (some addr)
      return .expr (.value $ .access $ .simple tensor) (.tensor dtype shape)
  | .tensor _ _ none =>
      throw "internal error: tensor argument does not have a name"

/-
Expressions

Note, expressions and statements are mutually recursive because a function call
expression may have to evaluate a user function (which is a list of
statements). Also, all of this is inherently non-terminating because the
original user program may not terminate. We could disallow non-termination in
NKI and then perhaps prove termination here, but this is TBD.
-/

mutual
partial def expr (e : Expr) : Trace Term :=
  withPos e.pos (expr' e.expr)

partial def expr' (e' : Expr') : Trace Term := do
  match e' with
  | .value v => value v
  | .var n => lookupName n
  | .tuple es => return .tuple (<- es.mapM expr)
  | .access e ix => access (<- expr e) (<- ix.mapM index)
  | .binOp op l r => binop op (<- expr l) (<- expr r)
  | .conj l r =>
      let l <- expr l
      if <- l.isTrue then return l else expr r
  | .disj l r =>
      let l <- expr l
      if <- l.isFalse then return l else expr r
  | .ifExp test tru fls =>
      if <- (<- expr test).isTrue
      then expr tru
      else expr fls
  | .call f args kwargs =>
      let f <- expr f
      fnCall f args kwargs

partial def optInt (e : Option Expr) : Trace (Option Int) := do
  match e with
  | none => return none
  | some e => return some (<- fromNKI? (<- expr e))

partial def index (i : Index) : Trace Term :=
  match i with
  | .coord e => expr e
  | .slice l u s => return .slice (<- optInt l) (<- optInt u) (<- optInt s)
  | .ellipsis => return .ellipsis

partial def keyword (kw : Keyword) : Trace (String × Term) :=
  match kw with
  | ⟨ name, e ⟩ => return (name, <- expr e)

partial def fnCall (f : Term) (args : List Expr) (kwargs : List Keyword) : Trace Term := do
  match f with
  | .builtin n _ self =>
      let f <- builtinFn n
      let args <- args.mapM expr
      args.forM checkAccess
      let kwargs <- kwargs.mapM keyword
      kwargs.forM fun (_,t) => checkAccess t
      let args := match self with
        | none => args
        | some t => t :: args
      f args kwargs
  | .source f =>
      -- Note: here is where we can't prove termination
      let args <- bindArgs f args kwargs
      let args <- args.mapM keyword
      args.forM fun (_,t) => checkAccess t (warnOnly := false)
      withSrc f.line f.source $ enterFun do
        args.forM fun kw => extend kw.1.toName kw.2
        match <- stmts f.body with
        | .ret t => return t
        | _ => return .none
  | _ => throw "not a callable type"

-- Statements

partial def iterator (i : Iterator) : Trace (List Term) := do
  match i with
  | .expr e => fromNKI? (<- expr e)
  | .range _ l u s =>
      let l : Int <- fromNKI? (<- expr l)
      let u : Int <- fromNKI? (<- expr u)
      let s : Int <- fromNKI? (<- expr s)
      return range l u s

partial def stmt (s : Stmt) : Trace Result :=
  withPos s.pos (stmt' s.stmt)

partial def stmts (l : List Stmt) : Trace Result := do
  match l with
  | [] => return .next
  | s :: l =>
    match <- stmt s with
    | .next => stmts l
    | r => return r

partial def stmt' (s' : Stmt') : Trace Result := do
  match s' with
  | .expr e => let _ <- expr e; return .next
  | .assert e =>
      if <- (<- expr e).isFalse then
        throw "assertion failed"
      return .next
  | .ret e => return .ret (<- expr e)
  | .declare .. => return .next
  | .letM (.var n) _ e => extend n (<- expr e); return .next
  | .letM (.tuple ..) .. => throw "internal error: complex pattern in trace"
  | .setM .. => throw "mutation not supported"
  | .ifStm e thn els =>
      if <- (<- expr e).isTrue
      then stmts thn
      else stmts els
  | .forLoop x iter body =>
      let ts : List Term <- iterator iter
      for t in ts do
        extend x t
        let res <- stmts body
        if res == .cont then continue
        if res == .brk then break
        if let .ret t := res then return .ret t
      return .next
  | .breakLoop => return .brk
  | .continueLoop => return .cont
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

private def shouldKeep : Name -> Bool
  | .str `neuronxcc.nki._pre_prod_kernels _ => true
  | .str `neuronxcc _ => false
  | .str `numpy _ => false
  | .str n _ => shouldKeep n
  | _ => true

private def filterGlobals (g : List Arg) : List Arg :=
  g.filter fun arg =>
    if let .str m _ := arg.name.toName then
      match g.find? fun a => a.name == m.toString with
      | some { value := ⟨ .var n, _ ⟩, .. } => shouldKeep n
      | some _
      | none => true
    else true

private def globals (k : Kernel) : Trace Unit := do
  let s <- get
  for f in k.funs do
    let n := f.name.toName
    if not (s.globals.contains n) then
      extend_global n (.source f)
  for g in filterGlobals k.globals do
    let name := g.name.toName
    if not (s.globals.contains name) then
      extend_global name (<- expr' g.value.expr)

private def processArgs (args : List Arg) : List Value × List Keyword := Id.run do
  let mut inputs : List Value := []
  let mut kws : List Keyword := []
  for ⟨ name, e ⟩ in args do
    match e with
    | ⟨ .value (.tensor s d _), pos ⟩ =>
      let t := .tensor s d name
      inputs := t :: inputs
      let e' := ⟨ .value t, pos ⟩
      kws := .mk name e' :: kws
    | _ => kws := .mk name e :: kws
  return (inputs.reverse, kws.reverse)

def traceKernel (k : Kernel) : Trace Core.Kernel := do
  globals k
  match k.funs.find? fun f => f.name == k.entry with
  | none => throw s!"function {k.entry} not found"
  | some f => do
      let (inputs, args) := processArgs k.args
      let res <- fnCall (.source f) [] args
      let inputs <- inputs.mapM value
      let inputs := Core.tensors inputs
      let outputs := Core.tensors res
      return {
        name := k.entry
        inputs := inputs
        outputs := outputs
        body := (<- get).body.toList
      }
