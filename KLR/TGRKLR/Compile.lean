import KLR.TGR.AST
import Lean
import TensorLib.Tensor
import KLR.TGRKLR.Operators

namespace KLR.TGRKLR

def Var := String
deriving Inhabited, Repr, BEq, Hashable

structure Ctx where
  typeEnv : List (KLR.TGR.Var × KLR.TGR.TensorTy)
  shapeEnv : List (KLR.TGR.Var × KLR.TGR.TensorTy)
  symEnv : List (KLR.TGR.Var × Var)
  vecEnv : List (KLR.TGR.Var × KLR.TGRKLR.VectorVar)
  gensymEnv : Nat := 0
  constants : List (Var × TensorLib.Tensor)
deriving Inhabited, Repr

abbrev Compile T := EStateM String Ctx T

def TensorK3 := String
def ScalarK3 := Immediate
def OperatorK3 := KLR.TGRKLR.Operator TensorK3 ScalarK3

def gensym : Unit → Compile String := fun _ => do
  let ctx ← get
  let sym := ctx.gensymEnv
  set { ctx with gensymEnv := ctx.gensymEnv + 1 }
  pure s!"{sym}"
def lookup (tgrVar : KLR.TGR.Var) : Compile Var := do
  let ctx ← get
  match ctx.symEnv.lookup tgrVar with
  | some klrVar => pure klrVar
  | none => panic! s!"Variable {tgrVar} not found in symbol environment."
def mapSym (k : KLR.TGR.Var) (v : Var) : Compile Var := do
  let ctx ← get
  set { ctx with symEnv := (k, v) :: ctx.symEnv }
  pure v
def gensymFrom (v : KLR.TGR.Var) : Compile String := do
  let sym ← gensym ()
  let _ ← mapSym v sym
  pure sym

def addConstant (v : Var) (t : TensorLib.Tensor) : Compile Unit := do
  let ctx ← get
  set { ctx with constants := (v, t) :: ctx.constants }

def aluOpOfBinOp :  KLR.TGR.BinaryOp → AluOp
  | .add  => .add
  | .sub  => .subtract
  | .mul  => .mult
  | .div  => .divide
  | .and  => .logical_and
  | .max  => .max
  | .cmp  => sorry
def aluOpOfUnOp : KLR.TGR.UnaryOp → ActivationFunc
  | .exp => .exp
  | .sqrt => .sqrt
  | .neg => sorry
  | .convert dtype => sorry

def makeTensor (t : Var) (ty : KLR.TGR.TensorTy) : TensorK3 := t

def lookupTy (n : KLR.TGR.Var) : Compile KLR.TGR.TensorTy := do
  match (← get).typeEnv.lookup n with | some ty => pure ty | none => throw s!"Type for {n} not found."
def tensorOfVar (v : Var) : Compile TensorK3 := do
  pure (makeTensor v (← lookupTy v))
def lower (v : KLR.TGR.Var) : Compile TensorK3 := do
  tensorOfVar (← gensymFrom v)
def fetch (v : KLR.TGR.Var) : Compile TensorK3 := do
  tensorOfVar (← lookup v)
def fresh (ty : KLR.TGR.TensorTy) : Compile TensorK3 := do
  let sym ← gensym ()
  pure (makeTensor sym ty)

def lowerVec (v : KLR.TGR.Var) : Compile VectorVar := do
  let sym ← gensymFrom v
  let ctx ← get
  set { ctx with vecEnv := (v, sym) :: ctx.vecEnv }
  pure sym
def fetchVec (v : KLR.TGR.Var) : Compile VectorVar := do
  match (← get).vecEnv.lookup v with
  | some vec => pure vec
  | none => throw s!"Vector {v} not found in vector environment."

structure CompileRule where
  impl : KLR.TGR.Function → Std.HashMap String KLR.TGR.Statement → Compile (Option (List OperatorK3))
  inputSize : Nat

namespace CompileRule
open Lean Std Elab Command Meta Term Parser
declare_syntax_cat pat
declare_syntax_cat patArg

syntax "<" pat ">": patArg
syntax term:max : patArg

syntax term:max patArg* : pat

syntax arrow := "->" <|> "-/>"

syntax (name := compileRule) "[Rule|" pat arrow term "]" : term

def replaceSubPatsWithFreshVars (patArgs : Array (TSyntax `patArg)) : TermElabM (Array (TSyntax `term)) := do
  patArgs.mapM fun x => do
    match x with
      | `(patArg|$v:term) => pure v
      | `(patArg|<$_:pat>) => pure $ mkIdent $ LocalContext.getUnusedName (← getLCtx) `temp
      | _ => panic! s!"Invalid pattern argument {x}"

def collectSubPats (vars : Array (TSyntax `term)) (patArgs : Array (TSyntax `patArg)) : List ((TSyntax `term) × (TSyntax `pat)) := Id.run do
  let mut result := []
  for (v, stx) in vars.zip patArgs do
    match stx with
    | `(patArg|<$p:pat>) => result := (v, p) :: result
    | _ => ()
  result

def mkDoBlock (doElems : TSyntaxArray `doElem) : MetaM (TSyntax `term) := do
  `(do $[$doElems:doElem]*)

def compileRuleMacroImpl : Syntax → TermElabM Syntax
  | `([Rule| $p:term $[$xs:patArg]* $arrow:arrow $body:term]) => do
    /- the list of vars to use as pattern variables in the top-level match.
    Nested patterns are replaces with fresh variables. -/
    let vars ← replaceSubPatsWithFreshVars xs
    /- for every nested pattern, adda tuple containing the name of the temporary
    variable it corresponds to and the syntax representing what it should match -/
    let mut (toMatch : List ((TSyntax `term) × (TSyntax `pat))) := collectSubPats vars xs
    -- emit the top-level match statement
    let mut (next : (TSyntax _) -> MetaM (TSyntax `term)) := (fun (k : TSyntax `term) =>
      `(fun ($(mkIdent `function) : KLR.TGR.Function) (table : Std.HashMap KLR.TGR.Var KLR.TGR.Statement) =>
        List.findSomeM? (fun $(mkIdent `dst) =>
          match table.get! $(mkIdent `dst) with
            | KLR.TGR.Statement.assign _ ($p $vars*) _ =>
              $k
            | _ => (pure Option.none : Compile _)
        ) table.keys
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
    | `(arrow|->) => `(return Option.some $body)
    | `(arrow|-/>) => `(return $body)
    | _ => panic! s!"Invalid arrow syntax {arrow}"
    let result ← next body
    dbg_trace s!"Expanded to {Syntax.prettyPrint result}"
    `({
      impl := $result,
      inputSize := $(quote ruleSize)
      : CompileRule
    })
  | _ => throwUnsupportedSyntax

@[term_elab compileRule]
def compileRuleElab : TermElab := Lean.Elab.Term.adaptExpander compileRuleMacroImpl

end CompileRule

def makeTable (l : List KLR.TGR.Statement) : Std.HashMap String KLR.TGR.Statement :=
  l.filterMap (fun x => match x with
    | KLR.TGR.Statement.assign dst _ _ => .some (dst, x)
    | _ => .none) |> Std.HashMap.ofList


open KLR.TGR.Operator
def run (rule : CompileRule) (statements : List KLR.TGR.Statement) : Option (List OperatorK3) :=
  let func := {name := "", inputs := [], outputs := [], statements := statements : KLR.TGR.Function}
  let table := makeTable statements
  match EStateM.run (rule.impl func table) default with
  | .ok result _ => result
  | .error e _ => panic! s!"Error running rule: {e}"

def ops : List OperatorK3 := [.max8 ⟨"a", "b"⟩]
#check [Rule| reshape <reshape a _> _ -> [.max8 ⟨← lower dst, ← fetch a⟩]]
#check [Rule| binaryOp op a b -> [.tensorTensor ⟨← lower dst, ← fetch a, ← fetch b, aluOpOfBinOp op⟩]]

#guard Option.isNone $ run [Rule| reshape _ _ -> ops]        [KLR.TGR.Statement.assign "x" (.arg 0) default]
#guard Option.isSome $ run [Rule| arg _ -> ops]              [KLR.TGR.Statement.assign "x" (.arg 0) default]
#guard Option.isNone $ run [Rule| reshape <arg _> _ -> ops]  [KLR.TGR.Statement.assign "b" (.reshape "a" default) default, KLR.TGR.Statement.assign "a" (.full default default) default]
#guard Option.isSome $ run [Rule| reshape <arg _> _ -> [.max8 ⟨ "a", "b" ⟩]] [KLR.TGR.Statement.assign "a" (.arg 0) default, KLR.TGR.Statement.assign "b" (.reshape "a" default) default]

def mkActivate (dst : TensorK3) (src : TensorK3) (op : ActivationFunc) : OperatorK3 :=
  .activate ⟨dst, src, .Idle, op, .float 1, .float 0, .float 0⟩

/- TODO: this should be in tensorlib -/
def floatOfLEBytArray (a : ByteArray) : Option Float32 := do
  match a.data.toList with
  | [b0, b1, b2, b3] =>
    let n := b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)
    Float32.ofBits n
  | _ => none
def floatOfScalarArray (t : TensorLib.Tensor) : Compile Float32 :=
  if t.shape == TensorLib.Shape.empty && t.dtype == TensorLib.Dtype.float32 then
    match floatOfLEBytArray t.data with
    | some f => pure f
    | none => throw s!"Failed to convert scalar array {t.shape} {t.dtype} to float32"
  else
    throw s!"Expected scalar array of type float32, got {t.shape} {t.dtype}"

def immOfScalarArray (t : TensorLib.Tensor) : Compile Immediate := do
  if t.dtype == TensorLib.Dtype.float32 then
    floatOfScalarArray t |>.map Immediate.float
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
    let intermediate ← fresh (← lookupTy a)
    /- TODO: is there a way to incorporate the inital value into the TensorReduce instruction? -/
    pure [
      /- perform reduction -/
      .tensorReduce ⟨intermediate, ← fetch a, aluOp, .X, false⟩,
      /- incorporate initial value -/
      .tensorScalar ⟨← lower dst, ← fetch a, ← immOfScalarArray initialValue, aluOp, .float 0, .bypass, .none⟩
    ]
  else
    panic! s!"reduction on non-last dimension {dim} of {a}"

def squeeze (a : TensorLib.Shape) : TensorLib.Shape :=
  { val := a.val.filter (fun x => x != 1) }

def mkTensorScalar (dst : TensorK3) (src : TensorK3) (imm : Immediate) (op : AluOp) : OperatorK3 :=
  .tensorScalar ⟨dst, src, imm, op, .float 0, .bypass, .none⟩

/- Assuming a is the vector and b is the tensor-/
def tryMakeBroadcastedTensorScalar (dst : KLR.TGR.Var) (vector : KLR.TGR.Var) (tensor : KLR.TGR.Var) (op : KLR.TGR.BinaryOp) : Compile (Option (List OperatorK3)) := do
  let natProd l := l.foldl (init := 1) (fun acc x => acc * x)
  let vectorTy ← lookupTy vector
  let tensorTy ← lookupTy tensor
  match vectorTy.shape.val.reverse, tensorTy.shape.val.reverse with
  | vectorHead :: vectorTail, _ :: tensorTail =>
    /- Make sure all but last dimensions match -/
    if natProd vectorTail == natProd tensorTail && vectorHead == 1 then
      let vec := ← gensymFrom vector
      pure $ .some [
        .makeVector ⟨vec, ← fetch vector⟩,
        mkTensorScalar (← lower dst) (← fetch tensor) (.vector vec) (aluOpOfBinOp op),
      ]
    else
      pure .none
  | _, _ => pure .none

/- TODO: this shoudl be in utils
Permute `l` according to the indices in `permutation`. -/
def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun dim => l[dim]?

def compileTranspose (dst : KLR.TGR.Var) (src : KLR.TGR.Var) (dims : List Nat) : Compile (List OperatorK3) := do
  let srcTy ← lookupTy src
  let srcShape := srcTy.shape.val
  let dstShape := permute srcShape dims |>.get!
  if srcShape == dstShape.reverse then
    pure [Operator.transpose ⟨← lower dst, ← fetch src⟩]
  else if srcShape == dstShape then
    pure [.identity ⟨← lower dst, ← fetch src⟩]
  else
    throw s!"Transpose of {srcShape} with dims {dims} does not match {dstShape.reverse}"

def compileRules := [
  -- binops
  [Rule| binaryOp op a b -> [.tensorTensor ⟨← lower dst, ← fetch a, ← fetch b, aluOpOfBinOp op⟩]],
  -- unops
  [Rule| unaryOp .exp a ->  [mkActivate (← lower dst) (← fetch a) .exp]],
  [Rule| unaryOp .sqrt a ->  [mkActivate (← lower dst) (← fetch a) .sqrt]],
  [Rule| unaryOp .neg a ->  [.tensorScalar ⟨← lower dst, ← fetch a, .float (-1), .mult, .float 0, .bypass, .none⟩]],
  [Rule| unaryOp (.convert type) _ -> panic! s!"unaryOp convert {type} not implemented"],

  -- mul by constant
  [Rule| binaryOp .mul <full n _> a ->  [.activate ⟨← lower dst, ← fetch a, .Idle, .copy, .float (← floatOfScalarArray n), .float 0, .float 0⟩]],
  -- max by constant
  [Rule| binaryOp .max <full n _> a ->  [.tensorScalar ⟨← lower dst, ← fetch a, .float (← floatOfScalarArray n), .max, .float 0, .bypass, .none⟩]],

  -- reductions
  [Rule| reductionOp op a init [dim] -> ← compileReduction function op a init dim dst],

  -- Reshapes
  [Rule| reshape a _ -> [.identity ⟨← lower dst, ← fetch a⟩]],

  -- broadcast+binop
  [Rule| binaryOp op <broadcast a _> b -/> (← tryMakeBroadcastedTensorScalar dst a b op)],

  -- transpose
  [Rule| transpose a dims -> ← compileTranspose dst a dims],

  -- matmul
  [Rule| batchMatmul a b -> [Operator.matmul (← lower dst) (← fetch a) (← fetch b)]],
]

def compile (p : KLR.TGR.Function) : Compile (List OperatorK3) := do
  sorry
