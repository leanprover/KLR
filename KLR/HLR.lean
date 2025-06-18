/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.Util
import SHerLOC
import TensorLib.Shape


namespace KLR.HLR

abbrev Shape := TensorLib.Shape

abbrev Var := String

abbrev Env T := List (Var × T)

namespace Env
def extend {T : Type} (env : Env T) (var : Var) (x : T) : Env T :=
  (var, x) :: env
def lookup  {T : Type} (env : Env T) (var : Var): Option T :=
  env.find? (fun (v, _) => v == var) |> .map (fun (_, x) => x)
def empty {T : Type} : Env T := []
end Env

abbrev ShapeEnv := Env Shape
abbrev GensymEnv := Env Nat

structure Ctx where
  environment : ShapeEnv
  gensymEnv : GensymEnv
  log : List String
deriving Inhabited, Repr

def empty : Ctx := .mk .empty .empty []

abbrev Compile T := EStateM String Ctx T

def log (msg : String) : Compile Unit :=
  modify (fun ctx => { ctx with log := msg :: ctx.log })

def assertShapeEq (shape1 shape2 : Shape) : Compile Unit := do
  if shape1 == shape2 then
    pure ()
  else
    .error s!"Shape mismatch: {shape1} != {shape2}"

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
  | reductionOp (op : BinaryOp) (init : Value) (a : Var) (dim : Nat)

  | matmul (a b : Var)
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
  | slice (a : Var) (start : Nat) (stop : Nat) -- ??
deriving Inhabited, Repr

def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun (dim : Nat) => l[dim]?

def outputShape (op : Operator) (env : ShapeEnv) : Compile Shape := do
  match op with
  | .binaryOp _ a b => do
      let aShape ← env.lookup  a
      let bShape ← env.lookup  b
      let _ ← assertShapeEq aShape bShape
      pure aShape
  | .unaryOp _ a => do
      let shape ← env.lookup  a
      pure shape
  | .reductionOp _ init a dim => do
      let aShape ← env.lookup  a
      pure (.mk (aShape.val.eraseIdx dim))
  | .matmul a b => do
      let aShape ← env.lookup  a
      let bShape ← env.lookup  b
      pure (.mk (aShape.val.eraseIdx 0 ++ bShape.val.eraseIdx 0))
  | .arange start stop step shape =>
      pure shape
  |  .concat (fst :: rest) dim => do
      let fstShape ← env.lookup fst
      let shapes ← rest.mapM (env.lookup  · )
      if shapes.all (fun s => (s.val.eraseIdx dim) == (fstShape.val.eraseIdx dim)) then
        let concattedLength : Nat := shapes.foldl (fun acc s => acc + s.val[dim]!) (fstShape.val[dim]!)
        pure (.mk (fstShape.val.set dim concattedLength))
      else
        .error "Shapes of tensors in concat do not match."
  | .concat [] _ => .error "Cannot concatenate an empty list of tensors."
  | .select cond a b => do
      let condShape ← env.lookup cond
      let aShape ← env.lookup  a
      let bShape ← env.lookup  b
      let _ ← assertShapeEq aShape bShape
      -- TODO: check condShape
      pure aShape
  | .full _ shape => pure shape
  | .transpose a dims => do
      let aShape ← env.lookup  a
      match permute aShape.val dims with
      | .some permutedShape => pure (.mk permutedShape)
      | none => .error "Invalid permutation dimensions."
  | .split_with_sizes a sizes => do
      sorry
  | .reshape a shape => pure shape
  | .broadcast a shape => pure shape
  | .const value shape => pure shape
  | .gather a indices => sorry
  | .slice a start stop => sorry

inductive Statement where
  | op (dest : Var) (op : Operator)
  | ret (name : Var)
deriving Inhabited, Repr

structure Program where
  statements : List Statement
deriving Inhabited, Repr, Nonempty

instance : ToString Operator where
  toString (op : Operator) : String :=
    match op with
    | .binaryOp binOp a b => s!"{repr binOp}({a}, {b})"
    | .unaryOp unOp a => s!"{repr unOp}({a})"
    | .reductionOp redOp init a dim => s!"{repr redOp}({repr init}, {a}, dim={dim})"
    | .matmul a b => s!"matmul({a}, {b})"
    | .arange start stop step shape => s!"arange({start}, {stop}, {step}, shape={shape})"
    | .concat tensors dim => s!"concat({", ".intercalate tensors}, dim={dim})"
    | .select cond a b => s!"select({cond}, {a}, {b})"
    | .full value shape => s!"full({repr value}, shape={shape})"
    | .transpose a dims => s!"transpose({a}, dims={dims})"
    | .split_with_sizes a sizes => s!"split_with_sizes({a}, sizes={sizes})"
    | .reshape a shape => s!"reshape({a}, shape={shape})"
    | .broadcast a shape => s!"broadcast({a}, shape={shape})"
    | .const values shape => s!"const({repr values}, shape={shape})"
    | .gather a indices => s!" gather({a}, indices={indices})"
    | .slice a start stop => s!"slice({a}, start={start}, stop={stop})"

instance : ToString Statement where
  toString (s : Statement) : String :=
    match s with
    | .op dest op => s!"{dest} = {op}"
    | .ret name => s!"return {name}"

instance : ToString Program where
  toString (p : Program) : String :=
    p.statements.map toString |> "\n".intercalate

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


-- Python pseudocode for the dotGeneral operation:
--    lhs_result_dimensions = [d for d in range(len(lhs.shape))
--                            if d not in lhs_batching_dimensions and d not in lhs_contracting_dimensions]
--    rhs_result_dimensions = [d for d in range(len(rhs.shape))
--                            if d not in rhs_batching_dimensions and d not in rhs_contracting_dimensions]
--
--    # Create transpose permutations according to the spec
--    lhs_transpose_perm = lhs_batching_dimensions + lhs_result_dimensions + lhs_contracting_dimensions
--    transposed_lhs_shape = [lhs.shape[x] for x in lhs_transpose_perm]
--
--    rhs_transpose_perm = rhs_batching_dimensions + rhs_result_dimensions + rhs_contracting_dimensions
--    transposed_rhs_shape = [rhs.shape[x] for x in rhs_transpose_perm]
--
--    # Get the shapes after transposition
--    batch_shape = [transposed_lhs_shape[i] for i in range(len(lhs_batching_dimensions))]
--    lhs_result_shape = [transposed_lhs_shape[i] for i in range(len(lhs_batching_dimensions),
--                                                               len(lhs_batching_dimensions) + len(lhs_result_dimensions))]
--    rhs_result_shape = [transposed_rhs_shape[i] for i in range(len(rhs_batching_dimensions),
--                                                               len(rhs_batching_dimensions) + len(rhs_result_dimensions))]
--    contracting_shape = [transposed_lhs_shape[i] for i in range(len(lhs_batching_dimensions) + len(lhs_result_dimensions),
--                                                                len(transposed_lhs_shape))]
--
--    batch_size = np.prod(batch_shape) if batch_shape else 1
--
--    # Calculate result shape
--    result_shape = batch_shape + lhs_result_shape + rhs_result_shape
--
--    lhs_result_size = np.prod(lhs_result_shape) if lhs_result_shape else 1
--    rhs_result_size = np.prod(rhs_result_shape) if rhs_result_shape else 1
--    contracting_size = np.prod(contracting_shape) if contracting_shape else 1
--    # ---
--    # Initialize result tensor
--    result = np.zeros(result_shape, dtype=lhs.dtype)
--
--    # Transpose lhs and rhs according to the specified dimensions
--    transposed_lhs = np.transpose(lhs, lhs_transpose_perm)
--    transposed_rhs = np.transpose(rhs, rhs_transpose_perm)
--
--    # Reshape tensors for easier computation
--    transposed_lhs_reshaped = transposed_lhs.reshape(batch_size, lhs_result_size, contracting_size)
--    transposed_rhs_reshaped = transposed_rhs.reshape(batch_size, rhs_result_size, contracting_size)
--    result_reshaped = result.reshape(batch_size, lhs_result_size, rhs_result_size)
--
--    # Perform the dot product computation
--    # We need to iterate over all batch indices and result indices
--    # Perform batched matrix multiplication
--    for b in range(batch_size):
--        # Extract slices for this batch
--        lhs_slice = transposed_lhs_reshaped[b]  # Shape: (lhs_result_size, contracting_size)
--        rhs_slice = transposed_rhs_reshaped[b]  # Shape: (rhs_result_size, contracting_size)
--
--        # Compute dot product: lhs_slice @ rhs_slice.T
--        result_reshaped[b] = lhs_slice @ rhs_slice.T
--
--    return result

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

def compileOp (m : StableHLO.Parsing.Operation) : Compile (List Statement) := do
  match m with
  | .stablehlo opCode inputValues _ inputAttributes outputs signature =>
    let makeUnOp := fun (op : UnaryOp) => do
      let a := inputValues[0]!
      let output ←  getOutputName outputs
      pure [Statement.op output (.unaryOp op a)]
    let makeBinOp := fun (op : BinaryOp) => do
      let a := inputValues[0]!
      let b := inputValues[1]!
      let output ←  getOutputName outputs
      let outputShape ←
        getSingleTensorOutputType signature.range
      modifyGet (fun ctx =>
        ((), { ctx with environment := ctx.environment.extend output outputShape }))
      pure [Statement.op output (.binaryOp op a b)]
    match opCode with
    | .constant =>  do
        log "constant"
        let valueAttr ← getAttribute inputAttributes "value"
        match valueAttr with
        | .mk _ (.mk (.tensor lit)  _) =>
          let shape ← getSingleTensorOutputType signature.range
          let outputName ← getOutputName outputs
          modifyGet (fun ctx =>
            ((), { ctx with environment := ctx.environment.extend outputName shape }))
          pure [.op outputName (.const lit shape)]
        | .mk _ (.mk _ _) => .error "Constant operation requires a 'value' attribute with tensor literal."
    | .dotGeneral => do
        log s!"DotGeneral -1"
        let (lhs_batching_dims, lhs_contracting_dims, rhs_batching_dims, rhs_contracting_dims) ←
          extractDotDimensionNumbers inputAttributes
        let lhs := inputValues[0]!
        let rhs := inputValues[1]!
        log s!"DotGeneral 0"
        let lhsShape ← getTensorInputType signature.domain 0
        let rhsShape ← getTensorInputType signature.domain 1
        log s!"DotGeneral 1"
        let lhsDims :=  List.range (TensorLib.Shape.ndim lhsShape)
        let rhsDims :=  List.range (TensorLib.Shape.ndim rhsShape)
        let lhs_result_dims := lhsDims.filter (fun i => !lhs_batching_dims.contains i && !lhs_contracting_dims.contains i)
        let rhs_result_dims := rhsDims.filter (fun i => !rhs_batching_dims.contains i && !rhs_contracting_dims.contains i)
        let lhs_transpose_perm := lhs_batching_dims ++ lhs_result_dims ++ lhs_contracting_dims
        let rhs_transpose_perm := rhs_batching_dims ++ rhs_result_dims ++ rhs_contracting_dims
        let lhs_transposed_shape := permute lhsShape.val lhs_transpose_perm
        let rhs_transposed_shape := permute rhsShape.val rhs_transpose_perm
        log s!"DotGeneral 2"
        match (lhs_transposed_shape, rhs_transposed_shape) with
        | (.some lhs_transposed_shape, .some rhs_transposed_shape) =>
          let batch_shape := lhs_transposed_shape.take lhs_batching_dims.length
          let lhs_result_shape := lhs_transposed_shape.drop lhs_batching_dims.length |>.take lhs_result_dims.length
          let rhs_result_shape := rhs_transposed_shape.drop rhs_batching_dims.length |>.take rhs_result_dims.length
          let contracting_shape := lhs_transposed_shape.drop (lhs_batching_dims.length + lhs_result_dims.length) |>
            List.take (lhs_transposed_shape.length - (lhs_batching_dims.length + lhs_result_dims.length))
          let batch_size := if batch_shape.isEmpty then 1 else batch_shape.foldl (fun acc d => acc * d) 1
          let result_shape := batch_shape ++ lhs_result_shape ++ rhs_result_shape
          let lhs_result_size := if lhs_result_shape.isEmpty then 1 else lhs_result_shape.foldl (fun acc d => acc * d) (1 : Nat)
          let rhs_result_size := if rhs_result_shape.isEmpty then 1 else rhs_result_shape.foldl (fun acc d => acc * d) (1 : Nat)
          let contracting_size := if contracting_shape.isEmpty then 1 else contracting_shape.foldl (fun acc d => acc * d) 1
          log s!"DotGeneral 3"
          --
          let outputName ← getOutputName outputs
          log s!"DotGeneral 4"
          let lhsTransposedName := lhs ++ "_transposed"
          let rhsTransposedName := rhs ++ "_transposed"
          let lhsReshapedName := lhs ++ "_reshaped"
          let rhsReshapedName := rhs ++ "_reshaped"
          let resultName := outputName ++ "_reshaped"
          log s!"DotGeneral 5"
          pure ([
            Statement.op lhsTransposedName (.transpose lhs lhs_transpose_perm),
            Statement.op rhsTransposedName (.transpose rhs rhs_transpose_perm),
            Statement.op lhsReshapedName (.reshape lhsTransposedName (.mk (batch_size :: lhs_result_size ::
              contracting_size :: []))),
            Statement.op rhsReshapedName (.reshape rhsTransposedName (.mk (batch_size :: rhs_result_size ::
              contracting_size :: []))),
          ] ++ ((List.range batch_size).flatMap (fun b =>
            let lhsSliceName := s!"{lhsReshapedName}_batch_{b}"
            let rhsSliceName := s!"{rhsReshapedName}_batch_{b}"
            let resultSliceName := s!"{resultName}_batch_{b}"
            Statement.op lhsSliceName (.slice lhsReshapedName b b) ::
            Statement.op rhsSliceName (.slice rhsReshapedName b b) ::
            Statement.op resultSliceName (.matmul lhsSliceName rhsSliceName) :: [])) ++
           [
            Statement.op outputName (.reshape resultName (.mk result_shape))
            ])
        | _ => .error "Invalid transposition permutations for dotGeneral operation."
    | .reshape => do
        log "reshape"
        let input := inputValues[0]!
        let outputShape ←  getSingleTensorOutputType signature.range
        let output ← getOutputName outputs
        modify (fun ctx =>
          { ctx with environment := ctx.environment.extend output outputShape })
        pure [.op output (.reshape input outputShape)]
    | .multiply =>
        log "multiply"
        makeBinOp .mul
    | .reduce =>
        log "reduce"
        pure [] -- TODO:
    | .maximum =>
        log "max"
        pure [] -- TODO:
    | .broadcastInDim => do
        log "broadcast"
        let input := inputValues[0]!
        let outputShape ←  getSingleTensorOutputType signature.range
        pure [.op input (.broadcast input outputShape)]
    | .subtract =>  makeBinOp .sub
    | .exponential => makeUnOp .exp
    | .divide =>  makeBinOp .div
    | .transpose => do
        log "transpose"
        let input := inputValues[0]!
        let dimsAttr ← getAttribute inputAttributes "permutation"
        match dimsAttr with
        | .mk _ (.mk (.array (.array64 arr)) _) => do
            let dims : List Nat := arr.map (fun (.mk _ n) => n)
            pure  [.op input (.transpose input dims)]
        | _ => .error "Transpose operation requires a 'permutation' attribute with an array of ints."
    | _ => .error s!"Unsupported operation: {repr opCode}"
  | .return ops _ => do
    log "return"
    pure [Statement.ret (",".intercalate ops)]
  | _ => .error "Unsupported operation type."

def compileFunc (f : StableHLO.Parsing.Function) : Compile Program :=
  match f.funcBody with
  | .mk _ body => do
    body.flatMapM compileOp |>.map Program.mk

def compileModule (m : StableHLO.Parsing.Module) : Compile Program := do
  match m.modFuncs with
  | [f] => compileFunc f
  | _ => .error "Only one function is supported for now."

def compile (m : List StableHLO.Parsing.Module) : (Except String Program × Ctx) :=
  let result := match  m with
    | [m] => compileModule m
    | _  => .error "Only one module is supported for now."
  match result.run empty with
  | .ok program s => ((.ok program), s)
  | .error err s => ((.error err), s)

end KLR.HLR
