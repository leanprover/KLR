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

import Cli
import KLR.Py.Gen
import KLR.Py.Pretty
import KLR.NKI.Simplify
import KLR.Compile.Pass
import KLR.Python

/-!
# AST Fuzzer for Simplify Pass Validation

Generates random Python ASTs, runs them through the simplify pass,
and outputs valid Python for seeds that pass simplification.
-/

open Cli
open KLR.Py
open KLR.Compile.Pass (runPasses runPass)
open System (FilePath)

-- Inhabited instance for Python.Expr'
instance : Inhabited KLR.Python.Expr' where
  default := .const .none

instance : Inhabited KLR.Python.Expr where
  default := { expr := .const .none, pos := { line := 0 } }

instance : Inhabited KLR.Python.Stmt' where
  default := .pass

instance : Inhabited KLR.Python.Stmt where
  default := { stmt := .pass, pos := { line := 0 } }

def defaultPos : KLR.Core.Pos := { line := 1 }

/-- Convert Py.Value to Python.Const -/
def valueToConst : Value → KLR.Python.Const
  | .none => .none
  | .bool b => .bool b
  | .int i => .int i
  | .float f => .float f
  | .string s => .string s
  | .ellipsis => .ellipsis

/-- Convert Py.UnaryOp to Python.UnaryOp -/
def unaryOpConv : UnaryOp → KLR.Python.UnaryOp
  | .pos => .uadd
  | .neg => .usub
  | .bitwiseNot => .invert
  | .lnot => .not

/-- Convert Py.BinOp to Python.BinOp (for non-comparison ops) -/
def binOpConv : BinOp → KLR.Python.BinOp
  | .land | .lor => .and  -- handled specially
  | .bitwiseOr => .or
  | .bitwiseXor => .xor
  | .bitwiseAnd => .and
  | .lshift => .lshift
  | .rshift => .rshift
  | .eq | .ne | .lt | .le | .gt | .ge => .add -- comparisons handled separately
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .pow => .pow
  | .floor => .floor
  | .matmul => .matmul

/-- Check if BinOp is a comparison -/
def isCompareOp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- Convert BinOp to CmpOp -/
def binOpToCmpOp : BinOp → KLR.Python.CmpOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge
  | _ => .eq  -- shouldn't happen

/-- Check if BinOp is a boolean op -/
def isBoolOp : BinOp → Bool
  | .land | .lor => true
  | _ => false

/-- Convert BinOp to BoolOp -/
def binOpToBoolOp : BinOp → KLR.Python.BoolOp
  | .land => .land
  | .lor => .lor
  | _ => .land  -- shouldn't happen

mutual
/-- Convert Py.Exp to Python.Expr -/
partial def pyExpToExpr (e : Exp) : KLR.Python.Expr :=
  { expr := pyExp'ToExpr' e.exp, pos := defaultPos }

partial def pyExp'ToExpr' : Exp' → KLR.Python.Expr'
  | .var name => .name name .load
  | .value v => .const (valueToConst v)
  | .unaryOp op x => .unaryOp (unaryOpConv op) (pyExpToExpr x)
  | .binOp op x y =>
    if isCompareOp op then
      .compare (pyExpToExpr x) [binOpToCmpOp op] [pyExpToExpr y]
    else if isBoolOp op then
      .boolOp (binOpToBoolOp op) [pyExpToExpr x, pyExpToExpr y]
    else
      .binOp (binOpConv op) (pyExpToExpr x) (pyExpToExpr y)
  | .tuple es => .tuple (es.map pyExpToExpr) .load
  | .list es => .list (es.map pyExpToExpr) .load
  | .ifExp test body orelse =>
      .ifExp (pyExpToExpr test) (pyExpToExpr body) (pyExpToExpr orelse)
  | .call f _ args =>
      .call (pyExpToExpr f)
            (args.filterMap fun a => if a.keyword.isNone then some (pyExpToExpr a.val) else none)
            (args.filterMap fun a => a.keyword.map fun k => ⟨some k, pyExpToExpr a.val, defaultPos⟩)
  | .access e indices => .subscript (pyExpToExpr e) (indicesToExpr indices) .load
  | .attr e field => .attr (pyExpToExpr e) field .load

partial def indexToExpr : Index → KLR.Python.Expr
  | .coord i => pyExpToExpr i
  | .slice l u step =>
      { expr := .slice (l.map pyExpToExpr) (u.map pyExpToExpr) (step.map pyExpToExpr)
      , pos := defaultPos }
  | .dynamic t _ _ => pyExpToExpr t

partial def indicesToExpr (indices : List Index) : KLR.Python.Expr :=
  match indices with
  | [idx] => indexToExpr idx
  | _ =>
    let exprs := indices.map indexToExpr
    { expr := .tuple exprs .load, pos := defaultPos }
end

/-- Convert Py.Pattern to Python.Expr -/
def pyPatternToExpr : Pattern → KLR.Python.Expr
  | .var name => { expr := .name name .store, pos := defaultPos }
  | .tuple pats => { expr := .tuple (pats.map pyPatternToExpr) .store, pos := defaultPos }

mutual
/-- Convert Py.Stmt to Python.Stmt -/
partial def pyStmtToStmt (s : Stmt) : KLR.Python.Stmt :=
  { stmt := pyStmt'ToStmt' s.stmt, pos := defaultPos }

partial def pyStmt'ToStmt' : Stmt' → KLR.Python.Stmt'
  | .exp e => .expr (pyExpToExpr e)
  | .imprt _ _ => .pass
  | .imprtFrom _ _ _ => .pass
  | .ret e => .ret (pyExpToExpr e)
  | .assign lhs _ rhs => .assign [pyExpToExpr lhs] (pyExpToExpr rhs)
  | .assert e => .assert (pyExpToExpr e) none
  | .funcDef _ => .pass  -- nested functions not supported
  | .ifStm cond thn _ els =>
      let thnStmts := thn.map pyStmtToStmt
      let elsStmts := els.map (·.map pyStmtToStmt) |>.getD []
      .ifStm (pyExpToExpr cond) thnStmts elsStmts
  | .forLoop pat iter body =>
      .forLoop (pyPatternToExpr pat) (pyExpToExpr iter) (body.map pyStmtToStmt) []
  | .whileLoop cond body =>
      .whileLoop (pyExpToExpr cond) (body.map pyStmtToStmt) []
  | .pass => .pass
  | .breakLoop => .breakLoop
  | .continueLoop => .continueLoop
end

/-- Convert Py.FuncDef to Python.Fun -/
def pyFuncDefToFun (f : FuncDef) : KLR.Python.Fun := {
  name := f.name
  fileName := "generated.py"
  line := 1
  source := ""
  decorators := []
  args := {
    posonlyargs := []
    args := f.params.map (·.name)
    defaults := f.params.filterMap (·.dflt) |>.map pyExpToExpr
    vararg := none
    kwonlyargs := []
    kw_defaults := []
    kwarg := none
  }
  body := f.body.map pyStmtToStmt
}

/-- Generate random enum class -/
def genEnumClass (seed : Nat) (idx : Nat) : KLR.Python.Class :=
  let rng := (seed * 1103515245 + 12345 + idx * 7) % (2^31)
  let nMembers := (rng % 4) + 1
  let fields := (List.range nMembers).map fun i =>
    let val : Int := ((rng * (i + 1)) % 200 : Nat)
    ⟨some s!"MEMBER_{i}", { expr := .const (.int val), pos := defaultPos }, defaultPos⟩
  {
    name := s!"MyEnum_{idx}"
    bases := [{ expr := .name "Enum" .load, pos := defaultPos }]
    decorators := []
    fields := fields
    methods := []
  }

/-- Generate random NKIObject class with methods -/
def genNKIObjectClass (seed : Nat) (idx : Nat) : KLR.Python.Class :=
  let rng := (seed * 1103515245 + 12345 + idx * 13) % (2^31)
  let nFields := (rng % 3) + 1
  let fields := (List.range nFields).map fun i =>
    let val : Int := ((rng * (i + 1)) % 100 : Nat)
    ⟨some s!"field_{i}", { expr := .const (.int val), pos := defaultPos }, defaultPos⟩
  let nMethods := (rng % 2) + 1
  let methods : List KLR.Python.Fun := (List.range nMethods).map fun i =>
    let retVal : Int := ((rng + i) % 50 : Nat)
    let methodBody : KLR.Python.Stmt := {
      stmt := .ret { expr := .const (.int retVal), pos := defaultPos }
      pos := defaultPos
    }
    {
      name := s!"method_{i}"
      fileName := "generated.py"
      line := 1
      source := ""
      decorators := []
      args := { posonlyargs := [], args := ["self"], defaults := [], vararg := none, kwonlyargs := [], kw_defaults := [], kwarg := none }
      body := [methodBody]
    }
  {
    name := s!"MyClass_{idx}"
    bases := [{ expr := .name "NKIObject" .load, pos := defaultPos }]
    decorators := [{ expr := .name "dataclass" .load, pos := defaultPos }]
    fields := fields
    methods := methods
  }

/-- Convert Py.Prog to Python.Kernel for simplify -/
def pyProgToKernel (p : Prog) (entry : String) (seed : Nat) : KLR.Python.Kernel :=
  let funcs := p.stmts.filterMap fun s =>
    match s.stmt with
    | .funcDef f => some (pyFuncDefToFun f)
    | _ => none

  -- Generate enums and classes based on seed
  let rng := seed % (2^31)
  let nEnums := (rng % 3)
  let nClasses := ((rng / 3) % 3)
  let enums := (List.range nEnums).map (genEnumClass seed)
  let classes := (List.range nClasses).map (genNKIObjectClass seed)

  {
    entry := entry
    funcs := funcs
    classes := enums ++ classes
    args := []
    kwargs := []
    globals := []
    arch := 0
    grid := 1
    scheduleEdges := []
    flags := []
  }

/-- Try to run simplify on a generated program, return error if failed -/
def trySimplify (prog : Prog) (seed : Nat) : Option KLR.NKI.Kernel × Option String :=
  let kernel := pyProgToKernel prog "test_kernel" seed
  let result := runPasses (runPass (KLR.NKI.simplify kernel))
  match result.result with
  | some k => (some k, none)
  | none => (none, result.errors.get? 0)

/-- Generate Python code for an enum class -/
def enumClassToString (seed : Nat) (idx : Nat) : String :=
  let rng := (seed * 1103515245 + 12345 + idx * 7) % (2^31)
  let nMembers := (rng % 4) + 1
  let members := (List.range nMembers).map fun i =>
    let val := (rng * (i + 1)) % 200
    s!"    MEMBER_{i} = {val}"
  s!"class MyEnum_{idx}(Enum):\n{"\n".intercalate members}\n"

/-- Generate Python code for an NKIObject class -/
def nkiClassToString (seed : Nat) (idx : Nat) : String :=
  let rng := (seed * 1103515245 + 12345 + idx * 13) % (2^31)
  let nFields := (rng % 3) + 1
  let fields := (List.range nFields).map fun i =>
    let val := (rng * (i + 1)) % 100
    s!"    field_{i} = {val}"
  let nMethods := (rng % 2) + 1
  let methods := (List.range nMethods).map fun i =>
    let retVal := (rng + i) % 50
    s!"    def method_{i}(self):\n        return {retVal}"
  s!"@dataclass\nclass MyClass_{idx}(NKIObject):\n{"\n".intercalate fields}\n{"\n".intercalate methods}\n"

/-- Generate class/enum code based on seed -/
def genClassesCode (seed : Nat) : String :=
  let rng := seed % (2^31)
  let nEnums := rng % 3
  let nClasses := (rng / 3) % 3
  let enumCode := (List.range nEnums).map (enumClassToString seed) |> "\n".intercalate
  let classCode := (List.range nClasses).map (nkiClassToString seed) |> "\n".intercalate
  let imports := if nEnums > 0 || nClasses > 0 then "from enum import Enum\nfrom dataclasses import dataclass\n\nclass NKIObject: pass\n\n" else ""
  imports ++ enumCode ++ (if enumCode.isEmpty then "" else "\n") ++ classCode ++ (if classCode.isEmpty then "" else "\n")

/-- Generate and test a single seed -/
def generateAndTest (seed : Nat) (outputDir : String) (verbose : Bool) : IO Bool := do
  let prog := Gen.genProg seed
  match trySimplify prog seed with
  | (some _, _) =>
    -- Simplify succeeded, write the Python file with classes
    let classesCode := genClassesCode seed
    let funcCode := Gen.progToString prog
    let content := s!"# Generated from seed: {seed}\n\n{classesCode}{funcCode}"
    let path := FilePath.mk outputDir / s!"{seed}.py"
    IO.FS.writeFile path content
    return true
  | (none, err) =>
    if verbose then
      IO.println s!"✗ Seed {seed}: {err.getD "unknown error"}"
    return false

/-- Simple LCG for generating random seeds -/
def nextSeed (s : Nat) : Nat :=
  (s * 1103515245 + 12345) % (2^31)

/-- Main fuzzer command -/
def fuzz (p : Parsed) : IO UInt32 := do
  let outputDir := p.positionalArg! "output" |>.as! String
  let count := (p.flag? "count").map (·.as! Nat) |>.getD 100
  let initSeed ← match p.flag? "seed" with
    | some f => pure (f.as! Nat)
    | none => IO.rand 0 (2^31 - 1)

  IO.FS.createDirAll outputDir

  let mut passed := 0
  let mut failed := 0
  let mut rng := initSeed

  for _ in [:count] do
    let seed := rng
    rng := nextSeed rng
    if ← generateAndTest seed outputDir (p.hasFlag "verbose") then
      passed := passed + 1
      IO.println s!"✓ Seed {seed} passed"
    else
      failed := failed + 1

  IO.println s!"\nResults: {passed} passed, {failed} failed out of {count}"
  return 0

def fuzzCmd : Cmd := `[Cli|
  fuzz VIA fuzz;
  "Generate random ASTs and test simplify pass"

  FLAGS:
    n, count : Nat; "Number of programs to generate (default: 100)"
    s, seed : Nat; "Starting seed (default: 0)"
    v, verbose; "Print failed seeds"

  ARGS:
    output : String; "Output directory for passing programs"
]

def main (args : List String) : IO UInt32 := do
  fuzzCmd.validate args
