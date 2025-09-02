import KLR.K.K2.AST
import KLR.K.K3.CompileK3
import KLR.K.Operators
import Lean
import TensorLib.Tensor
import Util.Gensym

namespace KLR.K.K2

open KLR.TGR(TensorTy)

/- in K2:

* tile names, variable names, and hbm tensor names are globally unique
* patterns have their slowest moving dimension first (matches numpy)
* patterns are in terms of number of elements, not bytes
* offsets are in terms of bytes, not elements
-/

/- The compilation context for the K3->K2 pass. -/
structure Ctx where
  /- Maps HBM tensor names in K3 to their corresponding HbmTensor in K2. -/
  lowerEnv : List (K3.Var × HbmTensor) := default
  gensymEnv : GensymEnv := default
  /- A configurable size for tiling. Setting to a small value makes debugging easier.
  Should not be larger than 128.-/
  tileDim := 4
deriving Inhabited, Repr

instance : ToString Ctx where
  toString _ :=
    /- TODO: -/
    s!"Ctx (...)"

/- Compilation monad for K3->K2 pass -/
abbrev Compile T := EStateM String Ctx T

/- Generate a fresh, unused symbol -/
def gensym (suggestion : String) : Compile String := do
  let (name, env) := (← get).gensymEnv.gensym suggestion
  modify fun ctx => { ctx with gensymEnv := env }
  return name

def tileDim : Compile Nat := do
  pure (← get).tileDim

/- Fetches the HbmTensor for the K3 variable `v`. If a statement that assigns
to `v` has not been compiled yet, it throws an error. -/
def fetch (v : K3.Var) : Compile HbmTensor := do
  match (← get).lowerEnv.lookup v with | some ty => pure ty | none => throw s!"HbmTensor for {v} not found."

instance : Coe TensorLib.Dtype KLR.Core.Dtype where
  coe
  /- The panics here can be fixed by adding more dtypes to KLR.Core -/
  | .bool => panic! "bool not supported in KLR.Core"
  | .int8 => .int8
  | .int16 => .int16
  | .int32 => .int32
  | .int64 => .int64
  | .uint8 => .uint8
  | .uint16 => .uint16
  | .uint32 => .uint32
  | .uint64 => .uint64
  | .float32 => .float32
  | .float64 => panic! "float64 not supported in KLR.Core"

/- Compiles a K3 scalar to K2. The only interesting case is vector, but it's
not clear how to handle it yet. See `compileTensorScalar` for an explanation of why.-/
def lowerScalar (s : K3.ScalarK3) : Compile ScalarK2 := do
  match s with
  | .float f => pure $ .float f
  | .int n => pure $ .int n
  | .vector .. => throw s!"Vector scalars not supported in KLR.K.K2, got {s}."

/- Construct a simple sbuf tile that has one free dimension with stride 1 -/
def makeSbufTile (name : Var) (partitionSize freeSize : Nat) (dtype : TensorLib.Dtype) : TensorK2 :=
  {
    name,
    dtype,
    memory := .sbuf,
    parNum := partitionSize,
    freePattern := [⟨1, freeSize⟩]
  }
/- Construct a simple psum tile that has one free dimension with stride 1 -/
def makePsumTile (name : Var) (partitionSize freeSize : Nat) (dtype : TensorLib.Dtype) : TensorK2 :=
  {makeSbufTile name partitionSize freeSize dtype with memory := .psum}

/- Compiles a tensor-scalar operation between `src` and `imm0` that writes output to `dest`.

Note that, as with other functions in this file, currently the tensor size must be a multiple
of the globally-configured tile dimension. This restriction could be relaxed by adding a loop epilogue
that handles the last iteration specially. -/
def compileTensorScalar
  (dest src : K3.TensorK3)
  (imm0 : K3.ScalarK3) (op0 : KLR.Core.AluOp) (imm1 : K3.ScalarK3) (op1 : KLR.Core.AluOp)
  (reverse : TensorScalarReverseOps)
  : Compile (List StatementK2) := do
  /- We can lower a simple  q-/
  /- The product of all dimension sizes besides the last -/
  let leadingDimensionsSize := src.type.shape.val.take (src.type.shape.ndim - 1) |> List.foldl (· * ·) 1
  let dtypeSize := src.type.dtype.itemsize

  let tilePartitionSize ← tileDim
  let tileFreeSize := src.type.shape.val.getLast!
  let tileSize := tilePartitionSize * tileFreeSize

  if leadingDimensionsSize % tilePartitionSize != 0 then
    throw s!"compileTensorScalar: Source tensor {src.name} has a leading dimension size ({leadingDimensionsSize}) that is not a multiple of the partition size {tilePartitionSize}."

  let sourceHbmTensor ← fetch src.name
  let destHbmTensor ← fetch dest.name

  /- Create the SBUF tiles -/
  let sourceSbuf := makeSbufTile sourceHbmTensor.name tilePartitionSize tileFreeSize src.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tilePartitionSize tileFreeSize dest.type.dtype
  let vecTileName ← gensym "vector"
  let vector := makeSbufTile vecTileName tilePartitionSize 1 src.type.dtype

  let loopVar := "i"

  /- If the immediate is a real "immediate" value, like a single float or int, we can just embed it
  in the tensorScalar instruction.
  However, if it's a `vector` immediate, that really means we need to load some values into a SBUF
  region and then pass a pointer to that region to the tensorScalar instruction.-/
  let (imm0, statements) := match imm0 with
    | .float f => (K2.ScalarK2.float f, [])
    | .int n => (.int n, [])
    | .vector name _size _dtype =>
      let vecVar := "vec"
      (ScalarK2.var vecVar,
      [
        .load vector ⟨name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tilePartitionSize⟩]⟩,
        .assign vecVar (.address vecTileName)
      ])
  let imm1 ← lowerScalar imm1

  pure [
    StatementK2.loop loopVar 0 leadingDimensionsSize tilePartitionSize (
      [StatementK2.load sourceSbuf ⟨sourceHbmTensor.name, .expr .mult (.var loopVar) (.int (dtypeSize * tileFreeSize)), [⟨1,tileSize⟩]⟩] ++
      statements ++
      [StatementK2.op (.tensorScalar ⟨destSbuf, sourceSbuf, imm0, op0, imm1, op1, reverse⟩)] ++
      [StatementK2.store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int (dtypeSize * tileFreeSize)), [⟨1,tileSize⟩]⟩ destSbuf])
  ]

/- Compiles a loop that will process each element of srcTensor once and write it to destTensor, with
no particular guarantees on what that loop looks like. `body` is a callback that takes an SBUF
region that has part of srcTensor loaded into it and should emit instructions that write to the
indicated destination SBUF region, which will then be written to HBM. -/
def makeSingleTensorLoop
  (srcTensor destTensor : K3.TensorK3)
  (body : TensorK2 → TensorK2 → Compile (List StatementK2)) : Compile (List StatementK2) := do
  let tilePartitionSize ← tileDim
  let tileFreeSize ← tileDim
  let tileSize := tilePartitionSize * tileFreeSize
  let dtypeSize := srcTensor.type.dtype.itemsize

  if srcTensor.type.shape.count % tileSize != 0 then
    throw s!"singletensorloop: Source tensor {srcTensor.name} has a shape ({srcTensor.type})that is not a multiple of the tile size {tileSize}."

  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let sourceSbuf := makeSbufTile sourceHbmTensor.name tilePartitionSize tileFreeSize srcTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tilePartitionSize tileFreeSize destTensor.type.dtype

  let loopVar := "i"
  pure [
    .loop loopVar 0 srcTensor.type.shape.count tileSize (
      [.load sourceSbuf ⟨sourceHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩] ++
      (← body destSbuf sourceSbuf) ++
      [.store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩ destSbuf])
  ]

/- Like makeSingleTensorLoop, but iterates through two source tensors. -/
def makeDoubleTensorLoop
  (aTensor bTensor destTensor : K3.TensorK3)
  (body : TensorK2 → TensorK2 → TensorK2 → Compile (List StatementK2)) : Compile (List StatementK2) := do
  let tilePartitionSize ← tileDim
  let tileFreeSize ← tileDim
  let tileSize := tilePartitionSize * tileFreeSize
  let dtypeSize := aTensor.type.dtype.itemsize

  if aTensor.type.shape.count % tileSize != 0 then
    throw s!"singletensorloop: Source tensor {aTensor.name} has a shape ({aTensor.type})that is not a multiple of the tile size {tileSize}."

  let aHbmTensor ← fetch aTensor.name
  let bHbmTensor ← fetch bTensor.name
  let destHbmTensor ← fetch destTensor.name
  let aSbuf := makeSbufTile aHbmTensor.name tilePartitionSize tileFreeSize aTensor.type.dtype
  let bSbuf := makeSbufTile bHbmTensor.name tilePartitionSize tileFreeSize bTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tilePartitionSize tileFreeSize destTensor.type.dtype

  /- If the tensor is small enough, we can just load it all at once and process it. -/
  if aTensor.type.shape.count == tileSize then
    pure $ [.load aSbuf ⟨aHbmTensor.name, .int 0, [⟨1, tilePartitionSize * tileFreeSize * dtypeSize⟩]⟩] ++
           [.load bSbuf ⟨bHbmTensor.name, .int 0, [⟨1, tilePartitionSize * tileFreeSize * dtypeSize⟩]⟩] ++
           (← body aSbuf bSbuf destSbuf) ++
           [.store ⟨destHbmTensor.name, .int 0, [⟨1, tilePartitionSize * tileFreeSize * dtypeSize⟩]⟩ destSbuf]
  else
    let loopVar := "i"
    let loop := [
      .loop loopVar 0 aTensor.type.shape.count tileSize (
        [.load aSbuf ⟨aHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩] ++
        [.load bSbuf ⟨bHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩] ++
        (← body aSbuf bSbuf destSbuf) ++
        [.store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩ destSbuf])
    ]
    pure loop

/- Compiles a tensor reduction operation that reduces `srcTensor` into `destTensor` along the
dimension `opDim` using the operation `op`. -/
def compileTensorReduce
  (srcTensor destTensor : K3.TensorK3) (op : KLR.Core.AluOp) (opDim : TensorSubDim) (negated : Bool) : Compile (List StatementK2) := do
  /- Only support for reducing along the last axis of a tensor initially.-/
  if opDim != .X then
    throw s!"compileTensorReduce: Unsupported reduction dimension {repr opDim} in {repr srcTensor.name}."

  /- The size after collapsing all dimensions but the reduction dimension -/
  let srcTensorLeadingSize := srcTensor.type.shape.val.take (srcTensor.type.shape.ndim - 1) |> List.foldl (· * ·) 1
  /- The size of the reduction dimension -/
  let srcTensorFreeSize := srcTensor.type.shape.val.getLast!
  let dtypeSize := srcTensor.type.dtype.itemsize

  if srcTensorLeadingSize != destTensor.type.shape.count then
    throw s!"compileTensorReduce: Source tensor {srcTensor.name} has a leading dimension size ({srcTensorLeadingSize}) that does not match the destination tensor size ({destTensor.type.shape.count})."

  let tileDim ← tileDim
  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let sourceSbuf := makeSbufTile sourceHbmTensor.name tileDim srcTensorFreeSize srcTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tileDim 1 destTensor.type.dtype

  let loopVar := "i"
  pure [
    .loop loopVar 0 srcTensorLeadingSize tileDim
      [.load sourceSbuf ⟨sourceHbmTensor.name, .expr .mult (.var loopVar) (.int (dtypeSize * srcTensorFreeSize)), [⟨1,tileDim * srcTensorFreeSize⟩]⟩,
      .op (.tensorReduce ⟨destSbuf, sourceSbuf, op, opDim, negated⟩),
      .store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileDim⟩]⟩ destSbuf]
  ]

/-
Multiples a tensor of shape (B, I, J) with a tensor of shape (B, K, J) and stores the result in a tensor of shape (B, I, K).
The first dimension is treated as a batch dimension, and the last dimension of each tensor is the contracting dimension.
This is equivalent to the `A @ B.transpose` in numpy.

In psuedocode:
```
# simulate np.einsum("bij,bkj->bik", a, b)
def matmul(X,Y):
    b,i,j = X.shape
    _,k,_ = Y.shape
    destM = np.zeros((b,i,k))
    tile = 2
    for bReg in range(b):
        x = X[bReg]
        y = Y[bReg]
        dest = destM[bReg]
        for iReg in range(0,i,tile):
            for kReg in range(0,k,tile):
                destTile = dest[iReg:iReg+tile, kReg:kReg+tile]
                for jReg in range(0,j,tile):
                    xTile = x[iReg:iReg+tile, jReg:jReg+tile]
                    yTile = y[kReg:kReg+tile, jReg:jReg+tile]
                    destTile += xTile @ yTile.T
```
-/
def compileMatMul
  (destTensor aTensor bTensor : K3.TensorK3) : Compile (List StatementK2) := do

  let (batchSize, iSize, jSize) ← match aTensor.type.shape.val with
  | [batchSize, iSize, jSize] => pure (batchSize, iSize, jSize)
  | _ => throw s!"Matrix multiplication only supported for 3D tensors, got {aTensor.type.shape.ndim}D tensor {aTensor.name}."
  let (_, kSize, _) ← match bTensor.type.shape.val with
  | [b, k, j] =>
    if b != batchSize then
      throw s!"Batch size mismatch in matrix multiplication: {batchSize} != {b}."
    if jSize != j then
      throw s!"Inner dimension mismatch in matrix multiplication: {jSize} != {j}."
    pure (b, k, j)
  | _ => throw s!"Matrix multiplication only supported for 3D tensors, got {bTensor.type.shape.ndim}D tensor {bTensor.name}."

  let aHbmTensor ← fetch aTensor.name
  let bHbmTensor ← fetch bTensor.name
  let destHbmTensor ← fetch destTensor.name

  let tileSize := 2

  if iSize % tileSize != 0 || jSize % tileSize != 0 || kSize % tileSize != 0 then
    throw s!"compileMatMul: One or more tensor sizes are not multiples of the tile size {tileSize}: iSize={iSize}, jSize={jSize}, kSize={kSize}."

  let bVar ← gensym "b"
  let iVar ← gensym "i"
  let kVar ← gensym "k"
  let jVar ← gensym "j"
  let xOffsetVar ← gensym "xOffset"
  let yOffsetVar ← gensym "yOffset"
  let destOffsetVar ← gensym "destOffset"
  let iTiles := iSize / tileSize
  let jTiles := jSize / tileSize
  let kTiles := kSize / tileSize

  let aSbuf := makeSbufTile aHbmTensor.name tileSize tileSize aTensor.type.dtype
  let bSbuf := makeSbufTile bHbmTensor.name tileSize tileSize bTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tileSize tileSize destTensor.type.dtype
  pure [
    .loop bVar 0 batchSize 1 [
      .loop iVar 0 iTiles 1 [
        .loop kVar 0 kTiles 1 [
          .op (.memSet ⟨destSbuf, .float 0, 0⟩),
          .loop jVar 0 jTiles 1 [
            -- bVar * i * j + iVar * j * tileSize + jVar * tileSize
            .assign xOffsetVar
              (.expr .add
               (.expr .mult
                (.var bVar)
                (.int (iSize * jSize)))
               (.expr .add
                (.expr .mult
                  (.var iVar)
                  (.int (jSize * tileSize)))
                (.expr .mult
                  (.var jVar)
                  (.int tileSize)))),
            -- bVar * k * j + kVar * j * tileSize + jVar * tileSize
            .assign yOffsetVar
              (.expr .add
               (.expr .mult
                (.var bVar)
                (.int (kSize * jSize)))
               (.expr .add
                (.expr .mult
                  (.var kVar)
                  (.int (jSize * tileSize)))
                (.expr .mult
                  (.var jVar)
                  (.int tileSize)))),
            .load aSbuf ⟨aHbmTensor.name, .var xOffsetVar, [⟨jSize,tileSize⟩,⟨1,tileSize⟩]⟩,
            .load bSbuf ⟨bHbmTensor.name, .var yOffsetVar, [⟨jSize,tileSize⟩,⟨1,tileSize⟩]⟩,
            .op (.loadStationary ⟨aSbuf, false⟩),
            .ifzero (jVar)
              [.op (.matMul ⟨destSbuf, bSbuf, .first⟩)]
              [.op (.matMul ⟨destSbuf, bSbuf, .middle⟩)],
          ],
          -- bVar * i * k + iVar * k * tileSize + kVar * tileSize
          .assign destOffsetVar
            (.expr .add
              (.expr .mult
              (.var bVar)
              (.int (iSize * kSize)))
              (.expr .add
              (.expr .mult
                (.var iVar)
                (.int (kSize * tileSize)))
              (.expr .mult
                (.var kVar)
                (.int tileSize)))),
          .store ⟨destHbmTensor.name, .var destOffsetVar, [⟨kSize,tileSize⟩,⟨1,tileSize⟩]⟩ destSbuf
        ]
      ]
    ]
  ]

/- Compiles a copy from srcTensor to destTensor -/
def makeCopy (destTensor srcTensor : K3.TensorK3) : Compile (List StatementK2) := do
  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let size := srcTensor.type.shape.count
  pure [.dramToDram ⟨destHbmTensor.name, .int 0, [⟨1,size⟩]⟩ ⟨sourceHbmTensor.name, .int 0, [⟨1,size⟩]⟩]

/- Compiles a transpose with the dimension permutatation [1, 2, 0] -/
def compile120Transpose (srcTensor destTensor : K3.TensorK3) (shape : List Nat): Compile (List StatementK2) := do
  let tileDim ← tileDim
  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let sourceSbuf := makeSbufTile sourceHbmTensor.name tileDim tileDim srcTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tileDim tileDim destTensor.type.dtype

  let x := shape[0]!
  let y := shape[1]! * shape[2]!

  if x % tileDim != 0 then
    throw s!"compile120transpose: Source tensor {srcTensor.name} has a shape ({x}) that is not a multiple of the tile size {tileDim}."
  if y % tileDim != 0 then
    throw s!"compile120transpose: Source tensor {srcTensor.name} has a shape ({y}) that is not a multiple of the tile size {tileDim}."

  let rowVar := "row"
  let colVar := "col"
  pure [
    .loop rowVar 0 x tileDim (
      [.loop colVar 0 y tileDim [
        .load sourceSbuf ⟨sourceHbmTensor.name, .expr .add (.expr .mult (.var rowVar) (.int x)) (.var colVar), [⟨1,tileDim⟩]⟩,
        .op (.transpose ⟨destSbuf, sourceSbuf⟩),
        .store ⟨destHbmTensor.name, .expr .add (.expr .mult (.var colVar) (.int x)) (.var rowVar), [⟨1,tileDim⟩]⟩ destSbuf,
        ]
      ]
    )
  ]

/- Compiles a transpose with the dimension permutatation [2, 0, 1] -/
def compile201Transpose (srcTensor destTensor : K3.TensorK3) (shape : List Nat): Compile (List StatementK2) := do
  let tileDim ← tileDim
  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let sourceSbuf := makeSbufTile sourceHbmTensor.name tileDim tileDim srcTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tileDim tileDim destTensor.type.dtype

  let x := shape[0]! * shape[1]!
  let y := shape[2]!

  if x % tileDim != 0 || y % tileDim != 0 then
    throw s!"compile201transpose: Source tensor {srcTensor.name} has a shape that is not a multiple of the tile size {tileDim}."

  let rowVar := "row"
  let colVar := "col"
  let loop := [
    .loop rowVar 0 x tileDim (
      [.loop colVar 0 y tileDim [
        .load sourceSbuf ⟨sourceHbmTensor.name, .expr .add (.expr .mult (.var rowVar) (.int x)) (.var colVar), [⟨1,tileDim⟩]⟩,
        .op (.transpose ⟨destSbuf, sourceSbuf⟩),
        .store ⟨destHbmTensor.name, .expr .add (.expr .mult (.var colVar) (.int x)) (.var rowVar), [⟨1,tileDim⟩]⟩ destSbuf,
        ]
      ]
    )
  ]
  pure loop

def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun dim => l[dim]?

/-
Compiles a transpose operation for a tensor `src` to a tensor `dst` with the specified `dims` permutation.
-/
def compileTranspose (dst src : K3.TensorK3) (dims : List Nat) : Compile (List StatementK2) := do
  let shape := src.type.shape.val
  let goalShape := K3.permute shape dims |>.get!

  let onesBefore i := shape.take i |>.count 1
  let dimsSqueezed :=
    dims.filter (fun d => shape[d]! != 1)
    |>.map fun d => d - onesBefore d

  let shapeSqueezed := shape.filter (fun d => d != 1)
  let goalShapeSqueezed := goalShape.filter (fun d => d != 1)

  match dimsSqueezed with
  | [] => panic! s!"No dimensions to transpose for {src.name} to {dst.name}."
  | [0] => makeCopy dst src
  | [0, 1] => makeCopy dst src
  | [1, 0] =>
    let sourceHbmTensor ← fetch src.name
    let destHbmTensor ← fetch dst.name
    let (x, y) := (shapeSqueezed[0]!, shapeSqueezed[1]!)
    let (xReg, yReg) := ("x", "y")
    return [
      .loop xReg 0 x 1 [
        .loop yReg 0 y 1 [
          .dramToDram
            ⟨destHbmTensor.name,
              .expr .add
                (.expr .mult (.var yReg) (.int x))
                (.var xReg),
              [⟨1,1⟩]⟩
            ⟨sourceHbmTensor.name,
              .expr .add
                (.expr .mult (.var xReg) (.int y))
                (.var yReg),
              [⟨1,1⟩]⟩
        ]
      ]
    ]
  | [0, 1, 2] => makeCopy dst src
  | [_, _, _] =>
    /- We can always fall back to compiling a transpose by copying one element at a time and following the transpose pattern. -/
    let sourceHbmTensor ← fetch src.name
    let destHbmTensor ← fetch dst.name
    let (x, y, z) := (shapeSqueezed[0]!, shapeSqueezed[1]!, shapeSqueezed[2]!)
    let (xReg, yReg, zReg) := ("x", "y", "z")
    let destAccessExpr :=
      let (aReg, bReg, cReg) := permute [xReg, yReg, zReg] dimsSqueezed |>.get! |> fun x => (x[0]!, x[1]!, x[2]!)
      let (_, b, c) := permute [x, y, z] dimsSqueezed |>.get! |> fun x => (x[0]!, x[1]!, x[2]!)
      (ScalarK2.expr .add
        (.expr .mult (.var aReg) (.int (b * c)))
        (.expr .add (.expr .mult (.var bReg) (.int c)) (.var cReg)))
    return [
      .loop xReg 0 x 1 [
        .loop yReg 0 y 1 [
          .loop zReg 0 z 1 [
            .dramToDram
              ⟨destHbmTensor.name, destAccessExpr, [⟨1,1⟩]⟩
              ⟨sourceHbmTensor.name,
                .expr .add
                  (.expr .mult (.var xReg) (.int (y * z)))
                  (.expr .add
                    (.expr .mult (.var yReg) (.int z))
                    (.var zReg)),
                [⟨1,1⟩]⟩
          ]
        ]
      ]
    ]
  /- These are close to working, but are still buggy, so they're commented out for now. -/
  /-
  | [1, 0, 2] => do
    let (x,y,z) := (shapeSqueezed[0]!,shapeSqueezed[1]!,shapeSqueezed[2]!)
    let inputAp :=  [⟨y*z,x⟩,⟨z,y⟩,⟨1,z⟩]
    let outputAp := [⟨z,x⟩,⟨z*x,y⟩,⟨1,z⟩]
    pure [
      .dramToDram ⟨dst.name, .int 0, outputAp⟩ ⟨src.name, .int 0, inputAp⟩
    ]
  | [1, 2, 0] => compile120Transpose src dst shapeSqueezed
  | [2, 0, 1] => compile201Transpose src dst shapeSqueezed
  -/
  | _ => throw s!"Unsupported transpose shape {shapeSqueezed} to goal shape {goalShapeSqueezed}."

/- Compiles a K3 statement to a set of K2 operators. In general, this happens by expanding a single
K3 operator on a tensor of unbounded size into a loop that calls that operator repeatedly on tiles
of the tensor that have been loaded into SBUF. -/
def compileStatement (s : K3.OperatorK3) : Compile (List StatementK2) := do
  let statements ← match s with
  | .activate ⟨dst, src, accumCmd, op, scale, bias, imm⟩ =>
    if accumCmd != .Idle then
      throw s!"Unsupported accumulation command {repr accumCmd} in {repr s}"
    makeSingleTensorLoop src dst fun sbufDestination sbufSource => do
      pure [
        .op (.activate ⟨sbufDestination, sbufSource, accumCmd, op, ← lowerScalar scale, ← lowerScalar bias, ← lowerScalar imm⟩),
      ]
  | .tensorTensor ⟨dst, a, b, op⟩ =>
    makeDoubleTensorLoop a b dst fun sbufA sbufB sbufDestination => do pure [
      .op (.tensorTensor ⟨sbufDestination, sbufA, sbufB, op⟩),
    ]
  | .tensorScalar ⟨dst, src, imm0, op0, imm1, op1, reverse⟩ => compileTensorScalar dst src imm0 op0 imm1 op1 reverse
  | .tensorReduce ⟨dst, src, op, opDim, negated⟩ =>
    if opDim != .X then
      throw s!"Unsupported reduction dimension {repr opDim} in {repr s}"
    compileTensorReduce src dst op opDim negated
  | .reshapeP ⟨dst, src⟩ =>
    makeSingleTensorLoop src dst fun sbufDestination sbufSource => do pure [
      .op (.copy ⟨sbufDestination, sbufSource, .none⟩),
    ]
  | .transposeP ⟨dst, src, dims⟩ => compileTranspose dst src dims
  | .matmulP ⟨dst, a, b⟩ => compileMatMul dst a b
  | .identityP ⟨dst, src⟩ => makeCopy dst src
  | _ => panic s!"compileStatement: Unsupported operator {repr s}"
  pure $ (.comment s!"{s}") :: statements

/- Compiles a K3 program to K2 -/
def compileProgram (f : K3.FunctionK3) : Compile ProgramK2 := do
  /- Gather all tensors that are inputs or are written to during the program -/
  let mut tensors := []
  for op in f.statements do
    for target in targets op do
      let hbmTensor := ⟨← gensym target.name⟩
      modify fun ctx =>
        { ctx with lowerEnv := (target.name, hbmTensor) :: ctx.lowerEnv }
      tensors := (hbmTensor.name, target.type) :: tensors
  for input in f.inputs do
    let hbmTensor := ⟨← gensym input.name⟩
    modify fun ctx =>
      { ctx with lowerEnv := (input.name, hbmTensor) :: ctx.lowerEnv }

  let statements ← f.statements.flatMapM compileStatement
  let inputs ← f.inputs.mapM (fun v => do pure ((← fetch v.name).name, v.type))
  let outputs ← f.outputs.mapM (fun v => fetch v.name |>.map fun x => x.name)
  pure {
    name := f.name,
    tensors,
    inputs,
    outputs,
    statements := statements
  }

/- Compiles a K3 program to K2 -/
def compile (f : K3.FunctionK3) : (Except String ProgramK2) × Ctx :=
  let compiled := compileProgram f
  match compiled.run {} with
  | .ok ops s => (.ok ops, s)
  | .error err s => (throw err, s)
