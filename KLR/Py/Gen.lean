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

import KLR.Py.Basic
import KLR.Py.Pretty

/-!
# Random AST Generator for KLR.Py

Generates random Python ASTs based on the definitions in Basic.lean.
Used for fuzzing the simplify pass.
-/

namespace KLR.Py.Gen

-- Add Inhabited instances for AST types
instance : Inhabited Index where
  default := .coord default

instance : Inhabited Pattern where
  default := .var "x"

instance : Inhabited Stmt where
  default := ⟨{}, .pass⟩

structure GenState where
  seed : Nat
  varCounter : Nat := 0
  vars : List Ident := []
  deriving Inhabited

abbrev GenM := StateM GenState

def nextRand : GenM Nat := do
  let s ← get
  -- LCG parameters (same as glibc)
  let next := (s.seed * 1103515245 + 12345) % (2^31)
  set { s with seed := next }
  return next

def randNat (max : Nat) : GenM Nat := do
  if max == 0 then return 0
  let r ← nextRand
  return r % (max + 1)

def randInt (lo hi : Int) : GenM Int := do
  let range := (hi - lo).toNat + 1
  let r ← randNat range
  return lo + r

def randBool : GenM Bool := do
  let r ← randNat 1
  return r == 1

def randChoice [Inhabited α] (xs : List α) : GenM α := do
  match xs with
  | [] => return default
  | _ =>
    let idx ← randNat (xs.length - 1)
    return xs[idx]!

def freshVar : GenM Ident := do
  let s ← get
  let name := s!"v{s.varCounter}"
  set { s with varCounter := s.varCounter + 1, vars := name :: s.vars }
  return name

def pickVar : GenM Ident := do
  let s ← get
  match s.vars with
  | [] => freshVar
  | vs => randChoice vs

def span : Span := {}

def genValue : GenM Value := do
  let choice ← randNat 4
  match choice with
  | 0 => return .none
  | 1 => return .bool (← randBool)
  | 2 => return .int (← randInt (-100) 100)
  | 3 => return .float (Float.ofInt (← randInt (-100) 100))
  | _ => do
    let n ← randNat 99
    return .string s!"s{n}"

def unaryOps : List UnaryOp := [.pos, .neg, .bitwiseNot, .lnot]
def arithOps : List BinOp := [.add, .sub, .mul, .div, .mod, .pow, .floor]
def cmpOps : List BinOp := [.eq, .ne, .lt, .le, .gt, .ge]
def logicOps : List BinOp := [.land, .lor]
def bitOps : List BinOp := [.bitwiseOr, .bitwiseXor, .bitwiseAnd, .lshift, .rshift]
def allBinOps : List BinOp := arithOps ++ cmpOps ++ logicOps ++ bitOps

mutual
partial def genLeafExp : GenM Exp := do
  let choice ← randNat 3
  match choice with
  | 0 =>
    let s ← get
    if !s.vars.isEmpty then
      let v ← pickVar
      return ⟨span, .var v⟩
    else
      let v ← genValue
      return ⟨span, .value v⟩
  | 1 =>
    let v ← genValue
    return ⟨span, .value v⟩
  | _ =>
    -- Call with no args as leaf
    let fname ← randChoice (["f", "g", "h"] : List String)
    return ⟨span, .call ⟨span, .var fname⟩ [] []⟩

partial def genIndex (depth : Nat) : GenM Index := do
  let choice ← randNat 4
  match choice with
  | 0 | 1 =>
    let i ← genExp depth
    return .coord i
  | 2 =>
    -- Slice with expressions
    let hasL ← randBool
    let hasU ← randBool
    let l ← if hasL then some <$> genExp depth else pure none
    let u ← if hasU then some <$> genExp depth else pure none
    let step ← if (← randNat 3) == 0 then some <$> genExp depth else pure none
    return .slice l u step
  | _ =>
    -- Empty slice
    return .slice none none none

partial def genExp (depth : Nat) : GenM Exp := do
  if depth >= 5 then
    genLeafExp
  else
    let choice ← randNat 15
    match choice with
    | 0 => genLeafExp
    | 1 =>
      -- Unary op
      let op ← randChoice unaryOps
      let x ← genExp (depth + 1)
      return ⟨span, .unaryOp op x⟩
    | 2 | 3 | 4 =>
      -- Binary op (common)
      let op ← randChoice allBinOps
      let x ← genExp (depth + 1)
      let y ← genExp (depth + 1)
      return ⟨span, .binOp op x y⟩
    | 5 =>
      -- Nested binary ops
      let op1 ← randChoice allBinOps
      let op2 ← randChoice allBinOps
      let a ← genExp (depth + 1)
      let b ← genExp (depth + 1)
      let c ← genExp (depth + 1)
      let inner : Exp := ⟨span, .binOp op1 a b⟩
      return ⟨span, .binOp op2 inner c⟩
    | 6 =>
      -- Tuple
      let n ← randNat 3
      let es ← (List.range (n + 1)).mapM fun _ => genExp (depth + 1)
      return ⟨span, .tuple es⟩
    | 7 =>
      -- List
      let n ← randNat 3
      let es ← (List.range (n + 1)).mapM fun _ => genExp (depth + 1)
      return ⟨span, .list es⟩
    | 8 | 9 =>
      -- Conditional (common)
      let test ← genExp (depth + 1)
      let body ← genExp (depth + 1)
      let orelse ← genExp (depth + 1)
      return ⟨span, .ifExp test body orelse⟩
    | 10 | 11 =>
      -- Function call with args
      let fname ← randChoice (["f", "g", "h"] : List String)
      let nargs ← randNat 2
      let args ← (List.range (nargs + 1)).mapM fun _ => do
        let val ← genExp (depth + 1)
        return Arg.mk none val
      return ⟨span, .call ⟨span, .var fname⟩ [] args⟩
    | 12 =>
      -- Chained call: f(g(x))
      let f1 ← randChoice (["f", "g", "h"] : List String)
      let f2 ← randChoice (["f", "g", "h"] : List String)
      let inner ← genExp (depth + 1)
      let innerCall : Exp := ⟨span, .call ⟨span, .var f2⟩ [] [⟨none, inner⟩]⟩
      return ⟨span, .call ⟨span, .var f1⟩ [] [⟨none, innerCall⟩]⟩
    | 13 =>
      -- Subscript access
      let base ← genExp (depth + 1)
      let idx ← genIndex (depth + 1)
      return ⟨span, .access base [idx]⟩
    | _ =>
      -- Multi-index access: x[a, b] or x[a][b]
      let base ← genExp (depth + 1)
      let idx1 ← genIndex (depth + 1)
      let idx2 ← genIndex (depth + 1)
      let useMulti ← randBool
      if useMulti then
        return ⟨span, .access base [idx1, idx2]⟩
      else
        let first : Exp := ⟨span, .access base [idx1]⟩
        return ⟨span, .access first [idx2]⟩

partial def genPattern (depth : Nat) : GenM Pattern := do
  -- Simplify pass only supports simple variables in for-loops
  let v ← freshVar
  return .var v

partial def genStmt (depth : Nat) (inLoop : Bool) : GenM Stmt := do
  if depth >= 3 then
    -- At max depth, generate simple but meaningful statements
    let choice ← randNat 2
    match choice with
    | 0 =>
      let v ← freshVar
      let rhs ← genExp depth
      return ⟨span, .assign ⟨span, .var v⟩ none rhs⟩
    | 1 =>
      let e ← genExp depth
      return ⟨span, .ret e⟩
    | _ =>
      let e ← genExp depth
      return ⟨span, .exp e⟩
  let choice ← randNat 10
  match choice with
  | 0 | 1 =>
    -- Assignment (more common)
    let v ← freshVar
    let rhs ← genExp depth
    return ⟨span, .assign ⟨span, .var v⟩ none rhs⟩
  | 2 =>
    let e ← genExp depth
    return ⟨span, .ret e⟩
  | 3 | 4 =>
    -- If statement (more common)
    let cond ← genExp depth
    let thn ← genStmts (depth + 1) inLoop
    let hasElse ← randBool
    let els ← if hasElse then some <$> genStmts (depth + 1) inLoop else pure none
    return ⟨span, .ifStm cond thn [] els⟩
  | 5 | 6 =>
    -- For loop (more common)
    let pat ← genPattern 0
    let bound ← randNat 4
    let bound := bound + 1
    let iter : Exp := ⟨span, .call ⟨span, .var "range"⟩ [] [⟨none, ⟨span, .value (.int bound)⟩⟩]⟩
    let body ← genStmts (depth + 1) true
    return ⟨span, .forLoop pat iter body⟩
  | 7 =>
    let cond ← genExp depth
    let body ← genStmts (depth + 1) true
    return ⟨span, .whileLoop cond body⟩
  | 8 =>
    if inLoop then return ⟨span, .breakLoop⟩
    else
      let v ← freshVar
      let rhs ← genExp depth
      return ⟨span, .assign ⟨span, .var v⟩ none rhs⟩
  | 9 =>
    if inLoop then return ⟨span, .continueLoop⟩
    else
      let e ← genExp depth
      return ⟨span, .exp e⟩
  | _ =>
    let e ← genExp depth
    return ⟨span, .exp e⟩

partial def genStmts (depth : Nat) (inLoop : Bool) : GenM (List Stmt) := do
  let n ← randNat 2
  let n := n + 2  -- 2-4 statements
  (List.range n).mapM fun _ => genStmt depth inLoop
end

def genFuncDef (name : Ident := "test_kernel") (allowParams : Bool := true) : GenM FuncDef := do
  let nParams ← if allowParams then randNat 3 else pure 0
  let params ← (List.range nParams).mapM fun i => do
    let pname := s!"p{i}"
    modify fun s => { s with vars := pname :: s.vars }
    return Param.mk pname none none
  let body ← genStmts 0 false
  return {
    name := name
    typParams := []
    params := params
    returns := none
    body := body
    decorators := []
    whereBounds := []
  }

/-- Generate helper functions with varied signatures -/
def genHelperFuncs : GenM (List FuncDef) := do
  let nHelpers ← randNat 3
  (List.range nHelpers).mapM fun i => do
    modify fun s => { s with vars := [] }
    let nParams ← randNat 2
    let params ← (List.range nParams).mapM fun j => do
      let pname := s!"arg{j}"
      modify fun s => { s with vars := pname :: s.vars }
      return Param.mk pname none none
    let body ← genStmts 0 false
    return {
      name := s!"func_{i}"
      typParams := []
      params := params
      returns := none
      body := body
      decorators := []
      whereBounds := []
    }

def genProg (seed : Nat) : Prog :=
  let gen : GenM Prog := do
    -- Generate helper functions
    let helpers ← genHelperFuncs

    -- Generate main kernel function (no params to avoid "argument not supplied")
    modify fun s => { s with vars := [] }
    let mainFunc ← genFuncDef "test_kernel" false

    let helperStmts := helpers.map fun f => Stmt.mk span (.funcDef f)
    let mainStmt := Stmt.mk span (.funcDef mainFunc)

    return { file := s!"seed_{seed}.py", stmts := helperStmts ++ [mainStmt] }

  let (prog, _) := gen.run { seed := seed }
  prog

def progToString (p : Prog) : String :=
  s!"# Generated from seed (see filename)\n\n{p.prettyPrint}"

end KLR.Py.Gen
