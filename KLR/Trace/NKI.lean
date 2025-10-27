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
import KLR.NKI.Pretty
import KLR.Trace.Builtin
import KLR.Trace.ISA
import KLR.Trace.Term
import KLR.Trace.Types
import KLR.Trace.Lang
import KLR.Compile.Pass

/-
# NKI built-ins

This module defines the builtin constants used by tracing for NKI kernels.
-/
namespace KLR.Trace
open KLR.NKI

-- NKI environment, including constants and the names of builtin functions
-- TODO: these should be defined in Python, not here
def NKIEnv : List (Name × Term) :=
  [ module nki_
  , module nki_isa
  , module nki_lang
  , module nki_typing
  , module `math
  , module `numpy
  , const_int (.str (nl "tile_size") "pmax") 128
  , const_int (.str (nl "tile_size") "gemm_stationary_fmax") 128
  , const_int (.str (nl "tile_size") "gemm_moving_fmax") 512
  , const_int (.str (nisa "nc_version") "gen1") 1
  , const_int (.str (nisa "nc_version") "gen2") 2
  , const_int (.str (nisa "nc_version") "gen3") 3
  -- engines
  , const_var (nisa "unknown_engine")
  , const_var (nisa "tensor_engine")
  , const_var (nisa "vector_engine")
  , const_var (nisa "scalar_engine")
  -- TODO: these should probably be defined inside python
  -- however we can't define `sbuf = sbuf`, even when we
  -- supply the sbuf as keyword ourself and defining these
  -- as a plain string seems meaningless to a degree
  , const_var (nl "psum")
  , const_var (nl "sbuf")
  , const_var (nl "hbm")
  , const_var (nl "shared_hbm")
  , const_var (nl "private_hbm")
  ]

-- The result of a statement evaluation
inductive Result where
  | next | brk | cont | ret (t : Term)
  deriving Repr, BEq

-- range, but only in a for-loop context
private def range (start stop step : Int) : List Term :=
  if step = 0 then []
  else if 0 < step then
    if stop <= start then [] else
    if stop <= start + step then [.int start] else
    .int start :: range (start + step) stop step
  else -- step < 0
    if start <= stop then [] else
    if start + step <= stop then [.int start] else
    .int start :: range (start + step) stop step
  termination_by (stop - start).natAbs

-- Lookup a name, falling back to attribute if not found
private def lookupName' (name : Name) : Trace Term := do
  match <- lookup? name with
  | some t => return t
  | none =>
    match name with
    | .str .anonymous _ => throw "empty"
    | .str n id => (<- lookupName' n).attr id
    | _ => throw s!"{name} not found."

private def lookupName (name : Name) : Trace Term := do
  try lookupName' name
  catch | "empty" => throw s!"{name} not found!"
        | e => throw e

/-
Best effort checks for slice overflow

Currently this implementation will silently clip out-of-bounds slice patterns,
similar to Python and numpy. However, to aide developers we will (try to) warn
or fail if we detect an overflow. This function is applied to function
arguments.
-/
private def checkAccess (t : Term) (warnOnly : Bool := true) : Trace Unit := do
  match t with
  | .access (.basic b) => do
    let shape <- b.shape
    for (dim, ndx) in shape.toList.zip b.indexes do
      if dim < ndx.size then
        if warnOnly then warn "index overflow"
        else throw "index overflow"
  | _ => return ()

-- Values

def value : Value -> Trace Term
  | .none      => return .none
  | .bool b    => return .bool b
  | .int i     => return .int i
  | .float f   => return .float f
  | .string s  => return .string s
  | .tensor s dty (some name) => do
      let shape <- Core.Shape.fromList s
      let dtype <- fromNKI? (.string dty)
      let addr : Core.Address := {
        name := name
        memory := .hbm
        parSize := shape.parDim
        freeSize := shape.freeElements * dtype.size
      }
      let tensor <- Core.TensorName.make name dtype shape (some addr) (<- flags.address_rotation)
      return .access (.simple tensor)
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

-- look for class method (used for overloading)
def method? (t : Term) (fn : String) : Trace (Option Term) := do
  match t with
  | .ref name (.object cls) =>
    match <- lookup? (.str cls fn) with
    | some (.source ..) => return some (.method cls fn name)
    | _ => return none
  | _ => return none

def binopOverload? (t : Term) (op : BinOp) (right := false) : Trace (Option Term) := do
  let fn <- match op with
    | .land => return none
    | .lor => return none
    | .eq => pure "eq"
    | .ne => pure "ne"
    | .lt => pure "lt"
    | .le => pure "le"
    | .gt => pure "gt"
    | .ge => pure "ge"
    | .add => pure "add"
    | .sub => pure "sub"
    | .mul => pure "mul"
    | .div => pure "truediv"
    | .mod => pure "mod"
    | .pow => pure "pow"
    | .floor => pure "floordiv"
    | .lshift => pure "lshift"
    | .rshift => pure "rshift"
    | .or => pure "or"
    | .xor => pure "xor"
    | .and => pure "and"
  let fn := if right then s!"__r{fn}__" else s!"__{fn}__"
  method? t fn

mutual
partial def expr (e : Expr) : Trace Term :=
  withPos e.pos (expr' e.expr)

partial def expr' (e' : Expr') : Trace Term := do
  match e' with
  | .value v => value v
  | .var n => lookupName n
  | .tuple es => return .tuple (<- es.mapM expr)
  | .list es =>
      let es <- es.mapM expr
      let name <- genName `list
      extend_global name (.list es.toArray)
      return .ref name .list
  | .dict ks =>
      let ks <- ks.mapM keyword
      let name <- genName `dict
      extend_global name (.dict ks.toArray)
      return .ref name .dict
  | .access e ix =>
      let e <- expr e
      let ix <- ix.mapM index
      if let some m <- method? e "__getitem__" then
        fnCall m [.tuple ix] []
      else
        access e ix
  | .binOp op l r =>
      let l <- expr l
      let r <- expr r
      if let some m <- binopOverload? l op then
        fnCall m [r] []
      else if let some m <- binopOverload? r op (right := true) then
        fnCall m [l] []
      else
        binop op l r
  | .conj l r =>
      let l <- expr l
      if <- l.isFalse then return l else expr r
  | .disj l r =>
      let l <- expr l
      if <- l.isTrue then return l else expr r
  | .ifExp test tru fls =>
      if <- (<- expr test).isTrue
      then expr tru
      else expr fls
  | .call f args kwargs =>
      let f <- expr f
      fnCall f (<- args.mapM expr) (<- kwargs.mapM keyword)
  | .object c fs =>
      let fs <- fs.mapM keyword
      let name <- genName `obj
      extend_global name (.object c fs.toArray)
      return .ref name (.object c)
  | .format e false => return .string (<- (<- expr e).toStr)
  | .format e true => return .string (reprStr (<- expr e))
  | .joined es =>
      let es <- es.mapM expr
      let strs <- es.mapM fun
        | .string s => pure s
        | _ => throw "internal error: non-string found in f-string elaboration"
      return .string (.join strs)

partial def optInt (e : Option Expr) : Trace (Option Int) := do
  match e with
  | none => return none
  | some e => return some (<- fromNKI? (<- expr e))

partial def index (i : Index) : Trace Term :=
  match i with
  | .coord e => expr e
  | .slice l u s => return .slice ((<- optInt l).getD 0) (<- optInt u) ((<- optInt s).getD 1)
  | .ellipsis => return .ellipsis

partial def keyword (kw : Keyword) : Trace (String × Term) :=
  match kw with
  | ⟨ name, e ⟩ => return (name, <- expr e)

partial def callFn (f : Fun) (args : List (String × Term)) : Trace Term := do
  args.forM fun (_,t) => checkAccess t (warnOnly := false)
  withFile f.file f.line f.source $ enterFun f.name do
    args.forM fun kw => extend kw.1.toName kw.2
    match <- stmts f.body with
    | .ret t => return t
    | _ => return .none

-- Bind arguments to a Python function based on its signature.
-- See also: Simplify.lean which checks for varargs signatures
partial def bindArgs
        (f : Fun)
        (args : List Term)
        (kwargs : List (String × Term))
        : Trace (List (String × Term)) := do
  if args.length + kwargs.length > f.args.length then
    throw "too many arguments given (varargs not supported)"
  f.args.zipIdx.mapM fun ({name := x, dflt := d}, i) => do
    if h:args.length > i then
      pure ⟨x, args.get (Fin.mk i h)⟩
    else if let some t := kwargs.lookup x then
      pure (x, t)
    else if let some e := d then
      pure (x, <- expr e)
    else
      throw s!"argument '{x}' not supplied"

partial def fnCall
        (f : Term)
        (args : List Term)
        (kwargs : List (String × Term))
        : Trace Term := do
  match f with
  | .builtin n self =>
      let f <- builtinFn n
      args.forM checkAccess
      kwargs.forM fun (_,t) => checkAccess t
      let args := match self with
        | none => args
        | some t => t :: args
      f args kwargs
  | .source f =>
      -- Note: here is where we can't prove termination
      let args <- bindArgs f args kwargs
      callFn f args
  | .method cls func ref => do
      match <- lookup? (.str cls func) with
      | some (.source f) =>
        let ref := Term.ref ref (.object cls)
        let args <- bindArgs f (ref :: args) kwargs
        callFn f args
      | _ => throw s!"{func} is not a method of {cls}"
  | t => throw s!"'{Term.kindStr t}' is not a callable type"

-- Statements

partial def mutate (x e : Expr) : Trace Unit :=
  withPos x.pos do
  match x.expr with
  | .access x [i] =>
    match <- expr x with
    | .ref name .list =>
        if let .list a <- lookup name then
          let i <- index i
          let i : Nat <- fromNKI? i
          let e <- expr e
          if h : i < a.size then
            extend name (.list (a.set i e h))
            return ()
          else throw "index out of range"
        else throw "internal error: expecting list literal"
    | .ref name .dict =>
        if let .dict a <- lookup name then
          let i <- index i
          let i : String <- fromNKI? i
          let e <- expr e
          let a := AA.insert a i e
          extend name (.dict (AA.insert a i e))
          return ()
        else throw "internal error: expecting dictionary literal"
    | r@(.ref _ (.object cls)) =>
        if let some m <- method? r "__setitem__" then
          let _ <- fnCall m [<- index i, <- expr e] []
          return ()
        else
          throw s!"class {cls} does not have a __setitem__ method"
    | .tensor .. =>
        throw "Updating a tile with lvalue assignment is not allowed"
    | _ =>
        throw "Value is not modifiable"
  | .var (.str obj var) =>
    match <- lookup? obj with
    | some (.ref name (.object cls)) =>
      match <- lookup? name with
      | some (.object c fs) =>
        if c != cls then
          throw s!"internal error: ref mismatch {c} != {cls}"
        let fs := AA.insert fs var (<- expr e)
        extend_global name (.object c fs)
      | _ => throw s!"{obj}.{var} is immutable"
    | _ => throw s!"{obj}.{var} is immutable"
  | _ => throw "mutation not supported"

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

partial def scalar (e : Expr) : Trace String :=
  withPos e.pos do
    let rec getName (t : Term) : Trace String := do
      match t with
      | .bool true => getName (<- Isa.builtin_isa_register_alloc [.int 1] [])
      | .bool false => getName (<- Isa.builtin_isa_register_alloc [.int 0] [])
      | .int i => getName (<- Isa.builtin_isa_register_alloc [.int i] [])
      | .scalar n => return n.toString
      | _ => throw "expecting scalar value"
    getName (<- expr' e.expr)

partial def dynamic (l : List Stmt) : Trace Unit := do
  match <- stmts l with
  | .next => return ()
  | .brk => throw "break not allowed within dynamic loop"
  | .cont => throw "continue not allowed within dynamic loop"
  | .ret _ => throw "return not allowed within dynamic loop"

partial def stmt' (s' : Stmt') : Trace Result := do
  match s' with
  | .expr e => let _ <- expr e; return .next
  | .assert e msg =>
      if <- (<- expr e).isFalse then
        let msg <- msg.mapM expr
        match msg with
        | some $ .string m =>
          throw s!"assertion failed, {m}"
        | _ => throw "assertion failed"
      return .next
  | .ret e => return .ret (<- expr e)
  | .declare .. => return .next
  | .letM (.var n) _ e => extend n (<- expr e); return .next
  | .letM (.tuple ..) .. => throw "internal error: complex pattern in trace"
  | .setM x e _ => mutate x e; return .next
  | .ifStm e thn els =>
      match <- expr e with
      | .scalar n =>
          let trueLbl := (<- genName `then).toString
          let falseLbl := (<- genName `else).toString
          let endLbl := (<- genName `end).toString
          brnz n.toString trueLbl falseLbl
          endBlock
          -- then:
          let _ <- beginBlock trueLbl
          let _ <- stmts thn
          jmp endLbl
          endBlock
          -- else:
          let _ <- beginBlock falseLbl
          let _ <- stmts els
          jmp endLbl
          endBlock
          -- end:
          let _ <- beginBlock endLbl
          return .next
      | e =>
          if <- e.isTrue
          then stmts thn
          else stmts els
  | .forLoop x (.range .dynamic l u s) body => do
      let bodyLbl := (<- genName `body).toString
      let endLbl := (<- genName `exit).toString
      -- init:
      let _ <- beginBlock
      let l <- scalar l
      let u <- scalar u
      let s <- @fromNKI? Nat _ (<- expr s)
      extend x (.scalar l.toName)
      -- entry:
      let _ <- beginBlock
      brlt l u bodyLbl endLbl
      endBlock
      -- body:
      let _ <- beginBlock bodyLbl
      dynamic body
      -- AluAdd reg += s
      addImm l u s
      brlt l u bodyLbl endLbl
      endBlock
      -- end:
      let _ <- beginBlock endLbl
      return .next
  | .forLoop x iter body =>
      let ts : List Term <- iterator iter
      enterLoop x do
        for t in ts do
          extend x t
          let res <- stmts body
          if res == .cont then continue
          if res == .brk then break
          if let .ret t := res then return .ret t
        return .next
  | .breakLoop => return .brk
  | .continueLoop => return .cont
  | .whileLoop test body =>
      match <- expr test with
      | .scalar .. =>
        let bodyLbl := (<- genName `body).toString
        let endLbl := (<- genName `exit).toString
        -- entry:
        let _ <- beginBlock
        let s <- scalar test
        brnz s bodyLbl endLbl
        endBlock
        let _ <- beginBlock bodyLbl
        dynamic body
        brnz s bodyLbl endLbl
        endBlock
        -- end:
        let _ <- beginBlock endLbl
        endBlock
        return .next
      | _ =>
        repeat
          if <- (<- expr test).isFalse then break
          let res <- stmts body
          if res == .cont then continue
          if res == .brk then break
          if let .ret t := res then return .ret t
        return .next
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
    let n := f.name
    if not (s.globals.contains n) && shouldKeep n then
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


partial def lowerRes (t: Term) : Trace (List Core.Access) := do
  match t with
  | .access a => return [a]
  | .tuple ts => return <- ts.flatMapM lowerRes
  | .list l => return <- l.toList.flatMapM lowerRes
  | .ref r _ => return <- lowerRes (<- lookupName r)
  | _ => return [] -- all others invariants should not contain tensors

def traceKernel (k : Kernel) : Trace Core.Kernel := do
  let _ <- beginBlock (<- genName `main).toString
  addId
  globals k
  flags k.flags
  match k.funs.find? fun f => f.name == k.entry with
  | none => throw s!"function {k.entry} not found"
  | some f => do
      let (inputs, args) := processArgs k.args
      let res <- fnCall (.source f) [] (<- args.mapM keyword)
      let inputs <- inputs.mapM value
      let inputs := Core.tensors inputs
      let outputs := Core.tensors $ <- lowerRes res
      endBlock
      return {
        name := k.entry.toString
        inputs := inputs
        outputs := outputs
        body := (<- get).body.toList
      }
