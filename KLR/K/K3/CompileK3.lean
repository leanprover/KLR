import Lean
import KLR.TGR.AST
import KLR.K.Operators
import KLR.K.K3.AST
import KLR.Util.Gensym
import TensorLib.Tensor

namespace KLR.K.K3

open KLR.TGR(TensorTy)

/- in K3:

* tensor names are globally unique
-/

/- The compilation state -/
structure Ctx where
  /- the type of each variable in the input program -/
  typeEnv : List (KLR.TGR.Var × KLR.TGR.TensorTy)
  /- Translation from a TGR variable to the K3 variable it is lowered to -/
  symEnv : List (KLR.TGR.Var × TensorK3) := default
  /- The set of KLR variables that have been added to the symEnv
  bu that don't have an operator that assigns to them yet -/
  freeVars : List KLR.TGR.Var := default
  /- The kernels argument list -/
  args : List TensorK3 := default
  gensymEnv : GensymEnv := default
deriving Inhabited, Repr

def makeContext (f : KLR.TGR.Function) : Ctx :=
  let typeEnv := f.statements.filterMap (fun s => match s with
    | KLR.TGR.Statement.assign dst _ ty => .some (dst, ty)
    | _ => .none)
  { typeEnv := typeEnv }

instance : ToString Ctx where
  toString ctx :=
    s!"Ctx ( typeEnv := {ctx.typeEnv}, symEnv := {repr ctx.symEnv}, freeVars := {ctx.freeVars})"

/- Monad for this compilation phase -/
abbrev Compile T := EStateM String Ctx T

/- Generate a unique unused name -/
def gensym (suggestion : String) : Compile String := do
  let (name, env) := (← get).gensymEnv.gensym suggestion
  modify fun ctx => { ctx with gensymEnv := env }
  return name

/- Get the type of a variable in the source program. -/
def lookupTy (n : KLR.TGR.Var) : Compile KLR.TGR.TensorTy := do
  match (← get).typeEnv.lookup n with | some ty => pure ty | none => throw s!"Type for {n} not found."

/- Lowers a variable in TGR to a TensorK3 in K3, adding the mapping to the symbol environment.
This should be used in the context where `v` is being assigned to -/
def lower (v : KLR.TGR.Var) : Compile TensorK3 := do
  let ctx ← get
  match ctx.symEnv.lookup v, ctx.freeVars.count v != 0 with
  | some tensor, true =>
    set { ctx with freeVars := ctx.freeVars.erase v }
    pure tensor
  | none, false => do
    let tensor := {name := ← gensym v, type := (← lookupTy v)}
    let ctx ← get
    set { ctx with symEnv := (v, tensor) :: ctx.symEnv }
    pure tensor
  | some _, false => panic! s!"Attempted to lower {v} that is not marked as free."
  | none, true => panic! s!"Variable {v} not found in symbol environment, but it is marked as free."

/- lowers an argument variable to a TensorK3 and adds it to the context's args list. -/
def lowerArg (v : KLR.TGR.Var) : Compile Unit := do
  let t ← lower v
  modify fun ctx => { ctx with args := t :: ctx.args }

/- Finds the TensorK3 corresponding to a variable in the source program. To be used
in the context where `v` is being read from. -/
def fetch (v : KLR.TGR.Var) : Compile TensorK3 := do
  match (← get).symEnv.lookup v with
  | some tensor => pure tensor
  | none => do
    let tensor := {name := ← gensym v, type := (← lookupTy v)}
    let ctx ← get
    set { ctx with freeVars := ctx.freeVars ++ [v], symEnv := (v, tensor) :: ctx.symEnv }
    pure tensor

/- A compilation rule is a function that takes a TGR variable and attempts to emit
K3 code that computes the value of that variable. The function also takes the
function being compiled and hash table of its statements. -/
structure CompileRule where
  impl : KLR.TGR.Function → Std.HashMap String KLR.TGR.Statement → KLR.TGR.Var → Compile (Option (List OperatorK3))
  /- The number of input variables that this rule consumes. -/
  inputSize : Nat
  /- A string representation of the rule, used for debugging. -/
  repr : String

/- Creates a hashmap from a list of statements, where the keys are the variable names
and the values are the statements that assign to those variables. -/
def makeTable (l : List KLR.TGR.Statement) : Std.HashMap String KLR.TGR.Statement :=
  l.filterMap (fun x => match x with
    | KLR.TGR.Statement.assign dst _ _ => .some (dst, x)
    | _ => .none) |> Std.HashMap.ofList

/- This namespace uses metaprogramming to define a custom syntax for writing compilation rules.
In short, the problem we're solving is that our programs are represented as a linear set of
statements in SSA form, but we want to pattern match on the statements as if they were a nested
tree structure in Lean. For example, to match a statement that reshapes an argument, we want to write
```
match op with
| reshape (arg _) _ => ...
```
but this doesn't work, we need to write instead
```
match op with
| reshape tmp _ =>
  match program.find tmp with
  | arg _ => ...
```
This metaprogramming allows us to write rules in a more ergonomic way, using angle brackets
to denote nested patterns.
```
| reshape <arg _> _ => ...
```
Skip to later in the file for more usage examples -/
namespace CompileRule
open Lean Std Elab Command Meta Term Parser
declare_syntax_cat pat
declare_syntax_cat patArg
syntax "<" pat ">": patArg
syntax term:max : patArg
syntax term:max patArg* : pat
syntax arrow := "->" <|> "-/>"
syntax (name := compileRule) "[Rule|" pat arrow term "]" : term

/- Replaces all nested patterns in the given pattern arguments with fresh variables. -/
def replaceSubPatsWithFreshVars (patArgs : Array (TSyntax `patArg)) : TermElabM (Array (TSyntax `term)) := do
  patArgs.mapM fun x => do
    match x with
      | `(patArg|$v:term) => pure v
      | `(patArg|<$_:pat>) => pure $ mkIdent $ LocalContext.getUnusedName (← getLCtx) `temp
      | _ => panic! s!"Invalid pattern argument {x}"

/- Collects all variables from the given pattern arguments and their corresponding patterns. -/
def collectSubPats (vars : Array (TSyntax `term)) (patArgs : Array (TSyntax `patArg)) : List ((TSyntax `term) × (TSyntax `pat)) := Id.run do
  let mut result := []
  for (v, stx) in vars.zip patArgs do
    match stx with
    | `(patArg|<$p:pat>) => result := (v, p) :: result
    | _ => ()
  result

/- Makes a do block from a list of do elements. -/
def mkDoBlock (doElems : TSyntaxArray `doElem) : MetaM (TSyntax `term) := do
  `(do $[$doElems:doElem]*)

/- The implementation of the `compileRule` macro. -/
def compileRuleMacroImpl : Syntax → TermElabM Syntax
  | `([Rule| $p:term $[$xs:patArg]* $arrow:arrow $body:term]) => do
    let pStr := ToString.toString p.raw
    let arrowStr := ToString.toString arrow.raw
    let xsStr := xs.map ToString.toString |>.toList |>.toString
    let repr ← `(s!"[Rule| {$(quote pStr)} {$(quote xsStr)} {$(quote arrowStr)} ...]")
    /- the list of vars to use as pattern variables in the top-level match.
    Nested patterns are replaces with fresh variables. -/
    let vars ← replaceSubPatsWithFreshVars xs
    /- for every nested pattern, adda tuple containing the name of the temporary
    variable it corresponds to and the syntax representing what it should match -/
    let mut (toMatch : List ((TSyntax `term) × (TSyntax `pat))) := collectSubPats vars xs
    -- emit the top-level match statement
    let mut (next : (TSyntax _) -> MetaM (TSyntax `term)) := (fun (k : TSyntax `term) =>
      `(fun ($(mkIdent `function) : KLR.TGR.Function) (table : Std.HashMap KLR.TGR.Var KLR.TGR.Statement) ($(mkIdent `dst) : Var) =>
          match table.get? $(mkIdent `dst) with
          | Option.some (KLR.TGR.Statement.assign _ ($p $vars*) _) =>
            $k
          | _ => (pure Option.none : Compile _)
      ))
    let mut ruleSize := 0;
    repeat do
      match toMatch with
      | (name, stx) :: r =>
        match (stx : TSyntax `pat) with
        | `(pat|$p:term $[$xs:patArg]*) =>
          -- make fresh variables for the nested patterns
          let vars ← replaceSubPatsWithFreshVars xs
          -- add nested patterns to the list of patterns to match
          toMatch := collectSubPats vars xs ++ toMatch
          -- emit a statement that matches the current pattern
          next := fun (k : TSyntax `term) =>
            `(match table.get? $name with
              | Option.none => (throw s!"Found missing variable {$name} in rule")
              | Option.some (KLR.TGR.Statement.assign dst ($p $vars*) _) =>
                if dst == $name then
                  $k
                else
                  (pure Option.none : Compile _)
              | _ => (pure Option.none : Compile _)) >>= next
          -- continue with the remaining patterns
          toMatch := r
          ruleSize := ruleSize + 1
        | _ => panic! s!"No patterns to match"
      | [] => break
    /- insert the final body that the user wants to evaluate -/
    let body ← match arrow with
    | `(arrow|->) => `(
      --dbg_trace s!"Successfully matched rule {$repr} with {$(quote ruleSize)} variables";
      return Option.some $body)
    | `(arrow|-/>) => `(
      --dbg_trace s!"Successfully matched rule {$repr} with {$(quote ruleSize)} variables";
      return $body)
    | _ => panic! s!"Invalid arrow syntax {arrow}"
    let result ← next body
    --dbg_trace s!"Expanded to {Syntax.prettyPrint result}"
    `({
      impl := $result,
      inputSize := $(quote ruleSize),
      repr := $repr
      : CompileRule
    })
  | _ => throwUnsupportedSyntax

/- We need to use `adaptExpander` since our macro needs to create fresh
variables, so it needs to run in a TermElabM context. -/
@[term_elab compileRule]
def compileRuleElab : TermElab := Lean.Elab.Term.adaptExpander compileRuleMacroImpl

end CompileRule

namespace CompileRuleExample
open KLR.TGR.Operator
def run (rule : CompileRule) (statements : List KLR.TGR.Statement) : Option (List OperatorK3) :=
  let func := {name := "", inputs := [], outputs := [], statements := statements : KLR.TGR.Function}
  let table := makeTable statements
  match EStateM.run (rule.impl func table "a") (makeContext func) with
  | .ok result _ => result
  | .error e _ => panic! s!"Error running rule: {e}"

def ops : List OperatorK3 := [.max8 ⟨{name:="a",type:=default}, {name:="b",type:=default}⟩]
#guard Option.isNone $ run [Rule| reshape _ _ -> ops]        [KLR.TGR.Statement.assign "x" (.arg 0) default]
#guard Option.isSome $ run [Rule| arg _ -> ops]              [KLR.TGR.Statement.assign "a" (.arg 0) default]
#guard Option.isNone $ run [Rule| reshape <arg _> _ -> ops]  [KLR.TGR.Statement.assign "b" (.reshape "a" default) default, KLR.TGR.Statement.assign "a" (.full default default) default]
#guard Option.isSome $ run [Rule| reshape <arg _> _ -> ops] [KLR.TGR.Statement.assign "b" (.arg 0) default, KLR.TGR.Statement.assign "a" (.reshape "b" default) default]
#guard Option.isSome $ run [Rule| reshape <arg _> _ -> ops] [KLR.TGR.Statement.assign "b" (.arg 0) default, KLR.TGR.Statement.assign "a" (.reshape "b" default) default]
end CompileRuleExample

/- Converts TGR binops to ISA ops -/
def aluOpOfBinOp :  KLR.TGR.BinaryOp → KLR.Core.AluOp
  | .add  => .add
  | .sub  => .subtract
  | .mul  => .mult
  | .div  => .divide
  | .and  => .logical_and
  | .max  => .max
  | .cmp  =>
    let _ : Nat := panic! s!"aluOpOfBinOp for cmp not implemented"
    sorry
/- Converts TGR unary ops to ISA ops -/
def aluOpOfUnOp : KLR.TGR.UnaryOp → ActivationFunc
  | .exp => .exp
  | .sqrt => .sqrt
  | .neg => panic! s!"aluOpOfUnOp for neg not implemented"
  | .convert dtype => panic! s!"aluOpOfUnOp for convert {dtype} not implemented"

/- Shorthand for creating an activation instruction with only one aluop used -/
def mkActivate (dst : TensorK3) (src : TensorK3) (op : ActivationFunc) : OperatorK3 :=
  .activate ⟨dst, src, .Idle, op, .float 1, .float 0, .float 0⟩

/- TODO: this should be in tensorlib -/
def floatOfLEBytArray (a : ByteArray) : Option Float32 := do
  match a.data.toList with
  | [b0, b1, b2, b3] =>
    let n := b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)
    Float32.ofBits n
  | _ => none
/- TODO: this should be in tensorlib -/
def floatOfScalarArray (t : TensorLib.Tensor) : Compile Float32 :=
  if t.shape == TensorLib.Shape.empty && t.dtype == TensorLib.Dtype.float32 then
    match floatOfLEBytArray t.data with
    | some f => pure f
    | none => throw s!"Failed to convert scalar array {t.shape} {t.dtype} to float32"
  else
    throw s!"Expected scalar array of type float32, got {t.shape} {t.dtype}"

/- Converts a TensorLib scalar array to an immediate value. -/
def immOfScalarArray (t : TensorLib.Tensor) : Compile ScalarK3 := do
  if t.dtype == TensorLib.Dtype.float32 then
    floatOfScalarArray t |>.map .float
  else
    throw s!"No implementation for immediate of type {t.dtype}."

def compileReduction (f : KLR.TGR.Function) (op : KLR.TGR.BinaryOp) (a : KLR.TGR.Var) (init : KLR.TGR.Var) (dim : Nat) (dst : KLR.TGR.Var) : Compile (List OperatorK3) := do
  /- TODO: factor out this function -/
  let lookupVar := fun v => f.statements.find? (fun s => match s with
    | .assign dst _ _ => dst == v
    | _ => false)
  let ndim := (← lookupTy a) |>.shape |>.ndim
  if dim + 1 == ndim then
    let aluOp := aluOpOfBinOp op
    let initialValue ← match lookupVar init with
      | some (.assign _ (.full value _) _) => pure value
      | _ => throw s!"Initial value for reduction {init} not found."
    let reducedShape := (← lookupTy a).shape.val.take (ndim - 1)
    let intermediate := {name := ← gensym "reductionIntermediate", type := ⟨⟨reducedShape⟩, (← lookupTy a).dtype⟩}
    /- TODO: is there a way to incorporate the inital value into the TensorReduce instruction? -/
    pure [
      /- perform reduction -/
      .tensorReduce ⟨intermediate, ← fetch a, aluOp, .X, false⟩,
      /- incorporate initial value -/
      .tensorScalar ⟨← lower dst, intermediate, ← immOfScalarArray initialValue, aluOp, .float 0, .bypass, .none⟩
    ]
  else
    panic! s!"reduction on non-last dimension {dim} of {a}"

/- Removes size 1 dimensions from a Tensor shape -/
def squeeze (a : TensorLib.Shape) : TensorLib.Shape :=
  { val := a.val.filter (fun x => x != 1) }

/- Shorthand for creating a tensor-tensor operator -/
def mkTensorScalar (dst : TensorK3) (src : TensorK3) (imm : ScalarK3) (op : KLR.Core.AluOp) : OperatorK3 :=
  .tensorScalar ⟨dst, src, imm, op, .float 0, .bypass, .none⟩

/- Attempts to make an instruction that broadcasts a single element of vector a
along the rows of tensor b -/
def tryMakeBroadcastedTensorScalar (dst : KLR.TGR.Var) (vector : KLR.TGR.Var) (tensor : KLR.TGR.Var) (op : KLR.TGR.BinaryOp) : Compile (Option (List OperatorK3)) := do
  let natProd l := l.foldl (init := 1) (fun acc x => acc * x)
  let vectorTy ← lookupTy vector
  let tensorTy ← lookupTy tensor
  match vectorTy.shape.val.reverse, tensorTy.shape.val.reverse with
  | vectorHead :: vectorTail, _ :: tensorTail =>
    /- Make sure all but last dimensions match -/
    if natProd vectorTail == natProd tensorTail && vectorHead == 1 then
      let vec := ← fetch vector
      pure $ .some [
        mkTensorScalar (← lower dst) (← fetch tensor) (.vector vec.name vec.type.shape.count vec.type.dtype) (aluOpOfBinOp op),
      ]
    else
      pure .none
  | _, _ =>
    pure .none

/- TODO: this should be in utils
Permute `l` according to the indices in `permutation`. -/
def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun dim => l[dim]?

def compileTranspose (dst : KLR.TGR.Var) (src : KLR.TGR.Var) (dims : List Nat) : Compile (List OperatorK3) := do
  let srcTy ← lookupTy src
  let srcShape := srcTy.shape.val
  let dstShape := permute srcShape dims |>.get!
  if srcShape == dstShape then
    pure [.identityP ⟨← lower dst, ← fetch src⟩]
  else
    pure [.transposeP ⟨← lower dst, ← fetch src, dims⟩]

/- For now, the ordering of these rules is important, as it determines what order they will be tried in.
Eventually, we want a heuristic that picks rules that consume more operators

Additionally, we probably want some way to mark the inputs to a rule as commutative so rules don't need to be duplciated -/
def compileRules := [
  -- mul by constant
  [Rule| .binaryOp .mul <.full n _> a ->  [.activate ⟨← lower dst, ← fetch a, .Idle, .copy, .float (← floatOfScalarArray n), .float 0, .float 0⟩]],
  [Rule| .binaryOp .mul a <.full n _> ->  [.activate ⟨← lower dst, ← fetch a, .Idle, .copy, .float (← floatOfScalarArray n), .float 0, .float 0⟩]],
  -- max by constant
  [Rule| .binaryOp .max <.full n _> a ->  [.tensorScalar ⟨← lower dst, ← fetch a, .float (← floatOfScalarArray n), .max, .float 0, .bypass, .none⟩]],
  [Rule| .binaryOp .max a <.full n _> ->  [.tensorScalar ⟨← lower dst, ← fetch a, .float (← floatOfScalarArray n), .max, .float 0, .bypass, .none⟩]],
  -- broadcast+binop (for broadcast in parallel dimension)
  [Rule| .binaryOp op <.broadcast a _> b -/> (← tryMakeBroadcastedTensorScalar dst a b op)],
  [Rule| .binaryOp op a <.broadcast b _> -/> (← tryMakeBroadcastedTensorScalar dst b a op)],

  -- binops
  [Rule| .binaryOp op a b -> [.tensorTensor ⟨← lower dst, ← fetch a, ← fetch b, aluOpOfBinOp op⟩]],
  -- unops
  [Rule| .unaryOp .exp a ->  [mkActivate (← lower dst) (← fetch a) .exp]],
  [Rule| .unaryOp .sqrt a ->  [mkActivate (← lower dst) (← fetch a) .sqrt]],
  [Rule| .unaryOp .neg a ->  [.tensorScalar ⟨← lower dst, ← fetch a, .float (-1), .mult, .float 0, .bypass, .none⟩]],
  [Rule| .unaryOp (.convert type) _ -> panic! s!"unaryOp convert {type} not implemented"],
  -- reductions
  [Rule| .reductionOp op a init [dim] -> ← compileReduction function op a init dim dst],
  -- Reshapes
  [Rule| .reshape a _ -> [.reshapeP ⟨← lower dst, ← fetch a⟩]],
  -- transpose
  [Rule| .transpose a dims -> ← compileTranspose dst a dims],
  -- matmul
  [Rule| .batchMatmul a b -> [.matmulP ⟨← lower dst, ← fetch a, ← fetch b⟩]],
  -- args
  [Rule| .arg _ -> let _ := (← lowerArg dst); []]
]

/- Compiles a TGR function to a K3 kernel by walking the TGR program in reverse
order and searching for an applicable compilation rule for each TGR variable.
Note that only variables used by a TGR statement will be compiled, so this pass
implicitly does dead code elimination. -/
partial def compileFunction (p : KLR.TGR.Function) : Compile FunctionK3 := do
  /- Start by finding the tensors that are returned by the TGR function
  and adding them to the free variable list so that we are assured they get
  compiled and are not treated as dead code. -/
  let retVars := p.statements.findSome? (fun s => match s with
    | KLR.TGR.Statement.ret v => .some v
    | _ => .none)
  let retVars ← match retVars with
  | .none => throw s!"No return value found in function {p.name}"
  | .some retVars => do
    retVars.mapM (fun var => fetch var)

  /- Acceleration structure for mapping variables to their defining statement -/
  let table := makeTable p.statements
  /- Walking the statement list backwards and compiling each statement
  so long as its in the freeVar list, indicating a later instruction requires it. -/
  let mut statements := []
  for statement in p.statements.reverse do
    match statement with
    | .assign target _ _ => do
      if (← get).freeVars.contains target then do
        let compiled ← compileRules.findSomeM? (fun rule => do
          match ← rule.impl p table target with
          | .some ops =>
            pure ops
          | .none => pure .none)
        match compiled with
        | .some ops => do
          statements := ops ++ statements
        | .none => throw s!"No rule found that matches variable {target}"
      else
        pure ()
    | _ => pure ()

  /- If the freeVars list isn't empty, it means that there are variables
  that were not assigned to by any operator, but are used by an operator. -/
  if !(← get).freeVars.isEmpty then
    throw s!"Not all free variables were assigned: {(← get).freeVars}"

  return {
    name := p.name,
    inputs := (← get).args,
    outputs := retVars,
    statements := statements
  }

/- Checks all tensors are assigned to before they are used. -/
def assertValidProgramOrder (f : FunctionK3) : Compile FunctionK3 := do
  let mut seen := f.inputs
  for statement in f.statements do
    for dep in dependencies statement do
      if !(seen.contains dep) then
        throw s!"Invalid program order: {dep} is used in {statement} but not seen yet."
    seen := (targets statement) ++ seen
  pure f

/- Compiles a TGR function to a K3 kernel, returning the compiled function and the compilation context. -/
def compile (f : KLR.TGR.Function) : (Except String FunctionK3) × Ctx :=
  let compiled := compileFunction f >>= assertValidProgramOrder
  match compiled.run (makeContext f) with
  | .ok func s =>
    (.ok func, s)
  | .error err s => (throw err, s)
