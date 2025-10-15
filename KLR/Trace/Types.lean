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

import KLR.Util
import KLR.Core
import KLR.NKI.Basic
import KLR.Compile.Pass

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
open KLR.Compile.Pass
export Core (Name)
export KLR.Compile.Pass (withPos withFile getPos warn message resetPassState)
export NKI (Pos BinOp)

abbrev SharedConstant := String × TensorLib.Tensor
abbrev SharedConstants := Array SharedConstant

/-
A term contains KLR expressions plus things that may exists at trace time.
References to modules, built-ins or user functions are only valid during
tracing. Also, none, strings, tuples and lists are only valid during tracing.
The ellipsis may be translated to a set of tensor indexes, or to a pass
statement depending on context. A slice is only valid in a tensor access
context in KLR, but may also be used with a list at trace time, or may float
around as a term for a while before it finds a home in a KLR term.

The ref variant is used to simulate mutable data types. The Name is a
value in the local environment that will be shared by all references to
the value.
-/
inductive RefType where
  | list | dict | object (cls : Name)
  deriving Repr, BEq

inductive Term where
  -- internals
  | module   : Name -> Term
  | builtin  : Name -> Option Term -> Term
  | ref      : Name -> RefType -> Term
  | source   : NKI.Fun -> Term
  | cls      : Name -> Term
  | object   : Name -> Array (String × Term) -> Term
  | method   : Name -> String -> Name -> Term
  -- expressions / values
  | var      : Name -> Term
  | none     : Term
  | bool     : Bool -> Term
  | int      : Int -> Term
  | float    : Float -> Term
  | string   : String -> Term
  | access   : Core.Access -> Term
  | tuple    : List Term -> Term
  | list     : Array Term -> Term
  | dict     : Array (String × Term) -> Term
  | tensor   : TensorLib.Tensor -> Term
  | scalar   : Name -> Term
  -- indexing
  | ellipsis : Term
  | slice    : Option Int -> Option Int -> Option Int -> Term
  | pointer  : Core.Address -> Term
  deriving Repr, BEq

namespace Term
def kindStr : Term → String
  | .module _ => "module"
  | .builtin _ _ => "builtin"
  | .ref _ _ => "ref"
  | .source _ => "source"
  | .cls n => s!"<class {n}>"
  | .object c _ => s!"<{c} object>"
  | .method c f r => s!"<{c}.{f} method (ref:{r})>"
  | .var _ => "var"
  | .none => "none"
  | .bool _ => "bool"
  | .int _ => "int"
  | .float _ => "float"
  | .string _ => "string"
  | .access _ => "access"
  | .tuple _ => "tuple"
  | .list _ => "list"
  | .dict _ => "dict"
  | .tensor _ => "tensor"
  | .scalar .. => "scalar"
  | .ellipsis => "ellipsis"
  | .slice _ _ _ => "slice"
  | .pointer _ => "pointer"
end Term

instance : Inhabited Term where
  default := .none

-- Only fully lowered terms are relevant
-- (we don't need to look inside tuples, etc.)
instance : Tensors Term where
  tensors
  | .access a => tensors a
  | _ => []

/-
Our state has a number for generating fresh names, the current source location
(for error reporting), and the global and local environments. The set of fully
traced statements is held in the `body` field, and there is an array of
warnings which may be shown to the user after tracing.
-/

abbrev Env := Std.HashMap Name Term

structure State where
  globals : Env := ∅
  locals : Env := ∅
  refs : Env := ∅
  body : Array Block := #[]
  tensorNames : Std.HashSet String := ∅
  sharedConstants : SharedConstants := #[]
  dynamicCtx : Bool := False
  label : Option String := none
  stmts : Array Stmt := #[]
deriving Repr

instance : Inhabited State where
  default := {}

abbrev Trace := Pass State

def genName (name : Name := `tmp) : Trace Name := do
  freshName name

-- add a new binding to the global environment
def extend_global (x : Name) (v : Term) : Trace Unit :=
  modify fun s => {s with globals := s.globals.insert x v}

-- add a new binding to the local environment
def extend (x : Name) (v : Term) : Trace Unit :=
  modify fun s => {s with locals := s.locals.insert x v}

-- lookup a name in the global environment
def lookup_global? (name : Name) : Trace (Option Term) := do
  return (<- get).globals.get? name

-- lookup a name in the environment
def lookup? (name : Name) : Trace (Option Term) := do
  match (<- get).locals.get? name with
  | some t => return t
  | none => lookup_global? name

def lookup (name : Name) : Trace Term := do
  match <- lookup? name with
  | none => throw s!"name {name} not found"
  | some x => return x

-- Enter a new local scope, replacing the local environment on exit.
def enter (m : Trace a) : Trace a := do
  let s ← get
  let locals := s.locals
  try m
  finally
    modify fun s => { s with locals := locals }

-- Enter a new function scope, removing all local bindings
def enterFun (m : Trace a) : Trace a := do
  let s ← get
  let locals := s.locals
  set { s with locals := ∅ }
  try m
  finally
    modify fun s => { s with locals := locals }

-- append fully traced statement
def add_stmt (stmt : Pos -> Stmt) : Trace Unit := do
  let pos <- getPos
  modify fun s => { s with stmts := s.stmts.push (stmt pos) }

def jmp (target : String) : Trace Unit := do
  add_stmt (.oper (.cmpBranch {
       reg1 := ""
       reg2 := ""
       imm  := 0
       op   := BrCmpOp.always
       trueLabel := target
       falseLabel := ""
    })
    (<- genName `jmp).toString)

def brnz (reg1 trueLabel falseLabel : String) : Trace Unit := do
  add_stmt (.oper (.cmpBranch {
       reg1
       reg2 := ""
       imm  := 0
       op   := BrCmpOp.ne_imm
       trueLabel
       falseLabel
    })
    (<- genName `brnz).toString)

def brlt (reg1 reg2 trueLabel falseLabel : String) : Trace Unit := do
  add_stmt (.oper (.cmpBranch {
       reg1
       reg2
       imm  := 0
       op   := BrCmpOp.lt_reg
       trueLabel
       falseLabel
    })
    (<- genName `brlt).toString)

def addImm (src dst : String) (imm : Int) : Trace Unit := do
  add_stmt (.oper (.registerAluOp {
       src
       dst
       imm
       op := AluOp.add
    })
    (<- genName `brnz).toString)


def endBlock (next : Option String := none) : Trace Unit := do
  -- Note: this statement may be discarded, which is correct
  if let some target := next then
    jmp target
  modify fun st =>
    match st.label with
    | none => { st with
        label := next
        stmts := #[]
      }
    | some lbl =>
      { st with
        body := st.body.push ⟨lbl, st.stmts.toList⟩
        label := next
        stmts := #[]
      }

def beginBlock (label : Option String := none) : Trace String := do
  let l := label.getD ((<- genName `label).toString)
  endBlock l
  return l

private def identity (n : Nat) : TensorLib.Tensor := Id.run do
  let dtype := TensorLib.Dtype.int8
  let shape := TensorLib.Shape.mk [n, n]
  let mut data := ByteArray.emptyWithCapacity (n * n)
  for i in [0:n] do
      for j in [0:n] do
        let value : UInt8 := if i == j then 1 else 0
        data := data.push value
  return { dtype := dtype, shape := shape, data := data }

def idName : Name := .num `identity 0

def addId : Trace Unit := do
  if let some _ <- lookup_global? idName then
    throw "identity already initialized"
  let dtype := .int8
  let shape := Core.Shape.mk 128 [128]
  let tensorName <- Core.TensorName.make idName.toString dtype shape none
  let id : KLR.Core.TensorRef := .abstract (.simple tensorName)
  let pos : Pos := { line := 0, column := 0 }
  let hbmInitName := <-genName
  let idAddr : Address := {
    name := hbmInitName.toString,
    memory := .hbm,
    parSize := 128
    freeSize := 128
    isShared := true
  }
  let idHbm : TensorName <- Core.TensorName.make hbmInitName.toString dtype shape idAddr
  let initStmt := Core.Stmt.oper (.ncDmaCopy {
    dst := id,
    src := .abstract (.simple idHbm),
    compute_op := .none,
    oobMode := .skip,
    dgeMode := 0,
  }) none pos
  let lbl := (<- genName `init).toString
  let idTensor :=  identity 128
  modify fun s => { s with
    body := #[Block.mk lbl [initStmt]] ++ s.body,
    sharedConstants := s.sharedConstants.push (hbmInitName.toString, idTensor)
  }
  extend_global idName (.access (.simple tensorName))

-- emit a message
--def message (msg : String) : Trace Unit := Pass.message
  --modify fun s => { s with messages := s.messages.push msg }

-- check and register a tensor name
def checkTensorName (name : String) : Trace Unit := do
  let st <- get
  if st.tensorNames.contains name then
    throw s!"Tensor name '{name}' already in use"
  set { st with tensorNames := st.tensorNames.insert name }

-- generate a unique tensor name
def genTensorName : Trace String := do
  let st <- get
  let mut n := st.tensorNames.size -- arbitrary
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
def tracer (g : List (Name × Term)) (m : Trace a) : PassM (SharedConstants × a) := do
  let initialState : State := { globals := .ofList g }
  runPassWith initialState do
    let x <- m
    let st <- get
    return (st.sharedConstants, x)

-- Truthiness of Terms following Python
namespace Term

private def clsName : Name -> String
  | .str _ n => n
  | n => n.toString

partial def toStr : Term -> Trace String
  | .module name => return name.toString
  | .builtin name _ => return name.toString
  | .ref name _ => do toStr (<- lookup name)
  | .source f => return f.name.toString
  | .cls c => return s!"<class {clsName c}>"
  | .object c fs => do
      let fs <- fs.mapM fun (n,t) => do pure s!"{n}:{<- t.toStr}"
      return s!"{clsName c}("++ ",".intercalate fs.toList ++")"
  | .method n id _ => return s!"<method {clsName n}.{id}>"
  | .var name => do toStr (<- lookup name)
  | .none => return "None"
  | .bool true => return "True"
  | .bool false => return "False"
  | .int i => return toString i
  | .float f => return toString f
  | .string s => return s
  | .access .. => return "<Access>"
  | .tuple ts => return "("++ ",".intercalate (<- ts.mapM toStr) ++")"
  | .list ts => return "["++ ",".intercalate (<- ts.toList.mapM toStr) ++"]"
  | .dict fs => do
      let fs <- fs.mapM fun (n,t) => do pure s!"{n}:{<- t.toStr}"
      return s!"\{"++ ",".intercalate fs.toList ++"}"
  | .ellipsis => return "..."
  | .slice a b c => return s!"slice({a},{b},{c})"
  | .pointer a => return s!"<Ptr({a.name})>"
  | .tensor .. => return "<Tensor>"
  | .scalar .. => return "<scalar>"

-- This is partial because the user could have created a heap graph
partial def isTrue (t : Term) : Trace Bool := do
  match t with
  -- internals
  | .module .. => return true
  | .builtin .. => return true
  | .ref name _ => isTrue (<- lookup name)
  | .source .. => return true
  | .cls .. => return true
  | .object .. => return true
  | .method .. => return true
  -- expressions / values
  | .var name => isTrue (<- lookup name)
  | .none => return false
  | .bool b => return b
  | .int i => return i != 0
  | .float f => return f != 0.0
  | .string s => return s.length > 0
  | .access .. => return true
  | .tuple l => return l.length > 0
  | .list a => return a.size > 0
  | .dict .. => return true
  -- indexing
  | .ellipsis ..
  | .slice ..
  | .pointer .. => throw "ambigous"
  | .tensor t =>
    if t.shape.count == 0 then
     return t.toList.toBool
    else if t.shape.count > 1 then
     throw "The truth value of an array with more than one element is ambiguous"
    else
     throw "The truth value of an empty array is ambiguous"
  | .scalar .. =>
    throw "boolean conversion of scalar not supported"

def isFalse (t : Term) : Trace Bool :=
  return not (<- t.isTrue)

end Term

-- Associative Arrays for dictionaries and objects

abbrev AA := Array (String × Term)

namespace AA

def lookup? (aa : AA) (key : String) : Option Term :=
  match aa.find? (fun item => item.fst == key) with
  | some (_, t) => some t
  | none => none

def insert (aa : AA) (key : String) (val : Term) : AA :=
  match aa.findIdx? fun item => item.fst == key with
  | none => aa.push (key, val)
  | some i => aa.modify i fun (k,_) => (k, val)

end AA
