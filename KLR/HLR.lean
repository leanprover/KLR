/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.Util
import SHerLOC
import TensorLib.Shape
import TensorLib.Slice

namespace KLR.HLR

abbrev Shape := TensorLib.Shape
abbrev Var := String

inductive BinaryOp where
  | mul
  | max
  | sub
  | div

deriving Inhabited, Repr

inductive UnaryOp where
  | exp
deriving Inhabited, Repr

inductive Value where
  | todo
deriving Inhabited, Repr

inductive Operator where
  | binaryOp (op : BinaryOp) (a b : Var)
  | unaryOp (op : UnaryOp) (a : Var)
  | reductionOp (op : BinaryOp) (a b : Var) (dim : Nat)

  | batchMatmul (a b : Var) (batchDims : Nat)
  | arange (start : Nat) (stop : Nat) (step : Nat) (shape : Shape)
  | concat (tensors : List Var) (dim : Nat)
  | select (cond a b : Var)
  | full (value : Value) (shape : Shape)
  | transpose (a : Var) (dims : List Nat)
  | split_with_sizes (a : Var) (sizes : List Nat) -- ??
  | reshape (a : Var) (shape : Shape)
  | broadcast (a : Var) (shape : Shape)
  | const (values : StableHLO.Parsing.DenseLiteral) (shape : Shape)
  | gather (a : Var) (indices : Var)
  | slice (a : Var) (dims : List TensorLib.Slice)
deriving Inhabited, Repr

inductive Statement where
  | comment (msg : String)
  | assign (dest : Var) (op : Operator) (shape : Shape)
  | loop (var : Var) (start stop : Nat) (body : List Statement)
  | ret (name : Var)
deriving Inhabited, Repr

structure Function where
  name : String
  inputs : List (Var × Shape)
  outputs : List Shape
  statements : List Statement
deriving Inhabited, Repr, Nonempty

structure Program where
  functions : List Function
deriving Inhabited, Repr, Nonempty

abbrev Env T := List (Var × T)

namespace Env
def extend {T : Type} (env : Env T) (var : Var) (x : T) : Env T :=
  (var, x) :: env
def lookup  {T : Type} (env : Env T) (var : Var): Option T :=
  env.find? (fun (v, _) => v == var) |> .map (fun (_, x) => x)
def empty {T : Type} : Env T := []
end Env

abbrev GensymEnv := Env Nat

structure Ctx where
  program : Program
  gensymEnv : GensymEnv
  log : List String
deriving Inhabited, Repr

def empty : Ctx := .mk (.mk []) .empty []

abbrev Compile T := EStateM String Ctx T

def log (msg : String) : Compile Unit :=
  modify (fun ctx => { ctx with log := msg :: ctx.log })

def gensym (label : String) : Compile Var := do
  let ctx ← get
  let nextId := match ctx.gensymEnv.lookup label with
    | some id => id + 1
    | none => 0
  modify (fun ctx => { ctx with gensymEnv := ctx.gensymEnv.extend label nextId })
  pure s!"{label}_{nextId}"

class FindShape (T : Type) where
  findShape : T → Var → Compile (Option Shape)

instance : FindShape (List Statement) where
  findShape statements var := do
    let found := statements.findSome? (fun x =>
      match x with
      | .assign v _ shape => if v == var then .some shape else .none
      | _ => .none)
    match found with
    | some shape => pure shape
    | none => pure .none

instance : FindShape Function where
  findShape f var := do
    let found := f.inputs.findSome? (fun (v, shape) => if v == var then .some shape else .none)
    match found with
    | some shape => pure shape
    | none => FindShape.findShape f.statements var

def addFunction (func : Function) : Compile Unit := do
  modify (fun ctx =>
    { ctx with program := { ctx.program with functions := ctx.program.functions ++ [func] } })

def assertShapeEq (shape1 shape2 : Shape) : Compile Unit := do
  if shape1 == shape2 then
    pure ()
  else
    .error s!"Shape mismatch: {shape1} != {shape2}"

def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun (dim : Nat) => l[dim]?

def dependencies (op : Operator) : List Var :=
  match op with
  | .binaryOp _ a b => [a, b]
  | .unaryOp _ a => [a]
  | .reductionOp _ a b _ => [a, b]
  | .batchMatmul a b _ => [a, b]
  | .arange _ _ _ _ => []
  | .concat tensors _ => tensors
  | .select cond a b => [cond, a, b]
  | .full _ _ => []
  | .transpose a _ => [a]
  | .split_with_sizes a _ => [a]
  | .reshape a _ => [a]
  | .broadcast a _ => [a]
  | .const _ _ => []
  | .gather a _ => [a]
  | .slice a _ => [a]

instance : ToString TensorLib.Slice where
  toString (s : TensorLib.Slice) : String :=
    let {start, stop, step, ..} := s
    let start := start.map toString |>.getD ""
    let stop := stop.map toString |>.getD ""
    let step := step.map toString |>.getD ""
    s!"{start}:{stop}:{step}"

instance : ToString TensorLib.Shape where
  toString (s : Shape) : String :=
    s.val.map toString |> fun x => "[" ++ "x".intercalate x ++ "]"

instance : ToString Operator where
  toString (op : Operator) : String :=
    match op with
    | .binaryOp binOp a b => s!"{repr binOp}({a}, {b})"
    | .unaryOp unOp a => s!"{repr unOp}({a})"
    | .reductionOp redOp a b dim => s!"reduce-{repr redOp}({a}, {b}, dim={dim})"
    | .batchMatmul a b batchDims => s!"matmul({a}, {b}, batchDims={batchDims})"
    | .arange start stop step shape => s!"arange({start}, {stop}, {step}, shape={shape})"
    | .concat tensors dim => s!"concat({", ".intercalate tensors}, dim={dim})"
    | .select cond a b => s!"select({cond}, {a}, {b})"
    | .full value shape => s!"full(..., shape={shape})"
    | .transpose a dims => s!"transpose({a}, dims={dims})"
    | .split_with_sizes a sizes => s!"split_with_sizes({a}, sizes={sizes})"
    | .reshape a shape => s!"reshape({a}, shape={shape})"
    | .broadcast a shape => s!"broadcast({a}, shape={shape})"
    | .const values shape => s!"const(..., shape={shape})"
    | .gather a indices => s!" gather({a}, indices={indices})"
    | .slice a dims => s!"slice({a}, dims={dims})"

def functionToString (f : Function) : Compile String := do
  let rec statementToString : Statement → Compile String := fun s => do
    match s with
    | .comment msg => pure s!"# {msg}"
    | .assign dest op shape => do
      let deps := dependencies op
      let depShapes := (← deps.mapM (FindShape.findShape f)) |> List.allSome
      let depShapes ← match depShapes with
        | some shapes => pure shapes
        | none => .error s!"Could not find shapes for dependencies: {deps}"
      let depShapesStr := depShapes.map toString |> ", ".intercalate
      pure s!"{dest} = {toString op} : ({depShapesStr}) -> {shape}"
    | .loop var start stop body => do
      let bodyStr := (← body.mapM statementToString) |> "\n".intercalate
      pure s!"for {var} in range({start}, {stop}):\n{bodyStr}"
    | .ret name => pure s!"return {name}"
  let inputsStr := f.inputs.map (fun (name, shape) => s!"{name} : {shape}") |> ", ".intercalate
  let outputsStr := f.outputs.map toString |> ", ".intercalate
  let statementsStr := (← f.statements.mapM statementToString) |> "\n".intercalate
  pure s!"def {f.name}({inputsStr}) -> ({outputsStr}):\n{statementsStr}"

def programToString (p : Program) : Compile String := do
  let functionsStr := (← p.functions.mapM functionToString)
  pure s!"# Program\n{functionsStr}"

instance : Coe StableHLO.Parsing.TensorType Shape where
  coe t := t.shape.map (fun dim => match dim with
    | .known d =>  d
    | .unknown => sorry) |> .mk

def getOutputName (outputs : List StableHLO.Parsing.ValueId) : Compile Var :=
  match outputs with
  | [output] => pure output
  | _ => .error "Function signature must have a single tensor output."

def getTensorInputType (sig : List StableHLO.Parsing.ValueType) (n : Nat): Compile Shape :=
  match sig[n]? with
  | .some (.tensorType t) => pure t
  | .some _ => .error s!"Function input {n} must have a tensor type."
  | _ => .error s!"Function signature must have at least {n + 1} tensor inputs. Instead, got  {repr sig}"
def getSingleTensorOutputType (sig : List StableHLO.Parsing.ValueType) : Compile Shape :=
  match sig with
  | [output] => match output with
    | .tensorType t => pure t
    | _ => .error "Function signature must have a single tensor output."
  | _ => .error "Function signature must have a single tensor output."

def getAttribute  (attrs : List StableHLO.Parsing.Attribute) (name : String) : Compile StableHLO.Parsing.Attribute :=
  match attrs.find? (fun (.mk id _) => id == name) with
  | some attr => pure attr
  | none => .error s!"Attribute '{name}' not found."

def getFieldValueMany (fields : List StableHLO.Parsing.StableHLORecordField) (name : String) : Compile (List Nat) :=
  match fields.find? (fun (.mk n _) => n == name) with
  | some (.mk _ (.many ns)) => pure ns
  | some _ => .error s!"Field '{name}' must be a list of integers."
  | none => pure []
def extractDotDimensionNumbers (attrs : List StableHLO.Parsing.Attribute) : Compile (List Nat × List Nat × List Nat × List Nat) := do
  let dotAttr ← getAttribute attrs "dot_dimension_numbers"
  match dotAttr with
  | .mk _ (.mk (.stableHLORecord fields) _) =>
    let lhs_batching_dims ← getFieldValueMany fields "lhs_batching_dimensions"
    let lhs_contracting_dims ← getFieldValueMany fields "lhs_contracting_dimensions"
    let rhs_batching_dims ← getFieldValueMany fields "rhs_batching_dimensions"
    let rhs_contracting_dims ← getFieldValueMany fields "rhs_contracting_dimensions"
    pure (lhs_batching_dims, lhs_contracting_dims, rhs_batching_dims, rhs_contracting_dims)
  | _ => .error "Attribute 'dot_dimension_numbers' must be a stableHLORecord."

def reduceFunctionToReduceOp (f : StableHLO.Parsing.InputFunc) : Compile (BinaryOp) := do
  match f with
  | .mk _ [.stablehlo .maximum _ _ _ _ _, .return _ _] => pure .max
  | .mk _ [.stablehlo .add _ _ _ _ _, .return _ _] => pure .sub
  | _ => .error ("Unable to match reduction function to a reduce operation." ++
    "Need to implement more cases or function calling.")

def compileOp (o : StableHLO.Parsing.Operation) : Compile (List Statement) := do
  match o with
  | .stablehlo opCode inputValues inputFunctions inputAttributes outputs signature =>
    let makeUnOp := fun (op : UnaryOp) => do
      let a := inputValues[0]!
      let output ←  getOutputName outputs
      let shape ← getSingleTensorOutputType signature.range
      pure [.assign output (.unaryOp op a) shape]
    let makeBinOp := fun (op : BinaryOp) => do
      let a := inputValues[0]!
      let b := inputValues[1]!
      let output ←  getOutputName outputs
      let outputShape ←
        getSingleTensorOutputType signature.range
      pure [.assign output (.binaryOp op a b) outputShape]
    match opCode with
    | .constant =>  do
        log "constant"
        let valueAttr ← getAttribute inputAttributes "value"
        match valueAttr with
        | .mk _ (.mk (.tensor lit)  _) =>
          let shape ← getSingleTensorOutputType signature.range
          let outputName ← getOutputName outputs
          pure [.assign outputName (.const lit shape) shape]
        | .mk _ (.mk _ _) => .error "Constant operation requires a 'value' attribute with tensor literal."
    | .dotGeneral => do
        let (lhsBatchingDims, lhsContractingDims, rhsBatchingDims, rhsContractingDims) ←
          extractDotDimensionNumbers inputAttributes
        let lhs := inputValues[0]!
        let rhs := inputValues[1]!
        let lhsShape ← getTensorInputType signature.domain 0
        let rhsShape ← getTensorInputType signature.domain 1
        let outputName ← getOutputName outputs
        let outputShape ← getSingleTensorOutputType signature.range
        let lhsDims :=  List.range (TensorLib.Shape.ndim lhsShape)
        let rhsDims :=  List.range (TensorLib.Shape.ndim rhsShape)
        let lhsResultDims := lhsDims.filter (fun i => !lhsBatchingDims.contains i && !lhsContractingDims.contains i)
        let rhsResultDims := rhsDims.filter (fun i => !rhsBatchingDims.contains i && !rhsContractingDims.contains i)
        let lhsTransposePerm := lhsBatchingDims ++ lhsResultDims ++ lhsContractingDims
        let rhsTransposePerm := rhsBatchingDims ++ rhsResultDims ++ rhsContractingDims
        let lhsTransposedShape := permute lhsShape.val lhsTransposePerm
        let rhsTransposedShape := permute rhsShape.val rhsTransposePerm
        match (lhsTransposedShape, rhsTransposedShape) with
        | (.some lhsTransposedShape, .some rhsTransposedShape) =>
          let batchShape := lhsTransposedShape.take lhsBatchingDims.length
          let lhsResultShape := lhsTransposedShape.drop lhsBatchingDims.length |>.take lhsResultDims.length
          let rhsResultShape := rhsTransposedShape.drop rhsBatchingDims.length |>.take rhsResultDims.length
          let contractingShape := lhsTransposedShape.drop (lhsBatchingDims.length + lhsResultDims.length) |>
            List.take (lhsTransposedShape.length - (lhsBatchingDims.length + lhsResultDims.length))
          let batchSize := if batchShape.isEmpty then 1 else batchShape.foldl (fun acc d => acc * d) 1
          let resultShape := batchShape ++ lhsResultShape ++ rhsResultShape
          let lhsResultSize := if lhsResultShape.isEmpty then 1 else lhsResultShape.foldl (fun acc d => acc * d) (1 : Nat)
          let rhsResultSize := if rhsResultShape.isEmpty then 1 else rhsResultShape.foldl (fun acc d => acc * d) (1 : Nat)
          let contractingSize := if contractingShape.isEmpty then 1 else contractingShape.foldl (fun acc d => acc * d) 1
          --
          let lhsTransposedName := lhs ++ "_transposed"
          let lhsTransposedShape ← (permute lhsShape.val lhsTransposePerm)
          let rhsTransposedName := rhs ++ "_transposed"
          let rhsTransposedShape ← (permute rhsShape.val rhsTransposePerm)
          let lhsReshapedName := lhs ++ "_reshaped"
          let lhsReshapedShape := [batchSize, lhsResultSize, contractingSize]
          let rhsReshapedName := rhs ++ "_reshaped"
          let rhsReshapedShape := [batchSize, rhsResultSize, contractingSize]
          let resultReshapedName := outputName ++ "_reshaped"
          let resultReshapedShape := [batchSize, lhsResultSize, rhsResultSize]
          pure ([
            .comment "Dot General Operation",
            .assign lhsTransposedName (.transpose lhs lhsTransposePerm) (.mk lhsTransposedShape),
            .assign rhsTransposedName (.transpose rhs rhsTransposePerm) (.mk rhsTransposedShape),
            .assign lhsReshapedName (.reshape lhsTransposedName (.mk lhsReshapedShape)) (.mk lhsReshapedShape),
            .assign rhsReshapedName (.reshape rhsTransposedName (.mk rhsReshapedShape)) (.mk rhsReshapedShape),
            .assign resultReshapedName (.batchMatmul lhsReshapedName rhsReshapedName batchShape.length) (.mk resultReshapedShape),
            .assign outputName (.reshape resultReshapedName (.mk resultShape)) outputShape,
          ])
        | _ => .error "Invalid transposition permutations for dotGeneral operation."
    | .reshape => do
        log "reshape"
        let input := inputValues[0]!
        let output ← getOutputName outputs
        let outputShape ← getSingleTensorOutputType signature.range
        pure [.assign output (.reshape input outputShape) outputShape]
    | .multiply =>
        log "multiply"
        makeBinOp .mul
    | .reduce =>
        log "reduce"
        let op ← reduceFunctionToReduceOp inputFunctions[0]!
        let output ← getOutputName outputs
        let outputShape ← getSingleTensorOutputType signature.range
        pure [.assign output (.reductionOp op inputValues[0]! inputValues[1]! 0) outputShape] -- TODO: init value
    | .broadcastInDim => do
        log "broadcast"
        let input := inputValues[0]!
        let output ← getOutputName outputs
        let outputShape ←  getSingleTensorOutputType signature.range
        pure [.assign output (.broadcast input outputShape) outputShape]
    | .subtract =>  makeBinOp .sub
    | .exponential => makeUnOp .exp
    | .divide =>  makeBinOp .div
    | .maximum =>  makeBinOp .max
    | .transpose => do
        log "transpose"
        let input := inputValues[0]!
        let dimsAttr ← getAttribute inputAttributes "permutation"
        let output ← getOutputName outputs
        let outputShape ← getSingleTensorOutputType signature.range
        match dimsAttr with
        | .mk _ (.mk (.array (.array64 arr)) _) => do
            let dims : List Nat := arr.map (fun (.mk _ n) => n)
            pure  [.assign output (.transpose input dims) outputShape]
        | _ => .error "Transpose operation requires a 'permutation' attribute with an array of ints."
    | _ => .error s!"Unsupported operation: {repr opCode}"
  | .return ops _ => do
    log "return"
    pure [Statement.ret (",".intercalate ops)]
  | _ => .error "Unsupported operation type."

def compileFunc (f : StableHLO.Parsing.Function) : Compile Unit :=
  match f.funcBody with
  | .mk args body => do
    let statements ← body.flatMapM compileOp
    let inputs ← args.mapM (fun (.mk name v) => do
      match v with
      | .tensorType t =>
        pure (name, t)
      | _ => .error s!"Function input {name} must have a tensor type.")
    let (outputs : List Shape) ← f.funcType.range.mapM (fun typ => do
      match typ with
      | .tensorType t => pure t
      | _ => .error "Function output must be a tensor type.")
    let func := Function.mk f.funcId inputs outputs statements
    addFunction func

def compileModule (m : StableHLO.Parsing.Module) : Compile Unit := do
  match m.modFuncs with
  | [f] => compileFunc f
  | _ => .error "Only one function is supported for now."

def compile (m : List StableHLO.Parsing.Module) : (Except String String) × Ctx :=
  let compiled := match m with
    | [m] => compileModule m
    | _  => .error "Only one module is supported for now."
  let str := compiled.bind (fun _ => do
    let ctx ← get
    let programStr ← programToString ctx.program
    pure programStr)
  match str.run empty with
  | .ok prog s => (.ok prog, s)
  | .error err s => (.error err, s)

end KLR.HLR
