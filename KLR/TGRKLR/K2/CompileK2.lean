import KLR.TGRKLR.K2.AST
import KLR.TGRKLR.K3.CompileK3
import KLR.TGRKLR.Operators
import Lean
import TensorLib.Tensor
import Util.Gensym

namespace KLR.TGRKLR.K2

open KLR.TGR(TensorTy)

/- This function is only needed for simulation. When interpreting a K1 program,
we want to treat all dtypes as size 1 to make things easier. -/
def dtypeSize (_dtypeSize : Nat) : Nat :=
  1

/- The compilation context for the K3->K2 pass. -/
structure Ctx where
  /- Maps HBM tensor names in K3 to their corresponding HbmTensor in K2. -/
  lowerEnv : List (K3.Var × HbmTensor)
  gensymEnv : GensymEnv := default
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
  | .vector .. => throw s!"Vector scalars not supported in KLR.TGRKLR.K2, got {s}."

/- Construct a simple sbuf tile that has one free dimension with stride 1 -/
def makeSbufTile (name : Var) (partitionSize freeSize : Nat) (dtype : TensorLib.Dtype) : TensorK2 :=
  {
    name,
    dtype,
    memory := .sbuf,
    parDim := partitionSize,
    freePattern := [⟨1, freeSize⟩]
  }
/- Construct a simple psum tile that has one free dimension with stride 1 -/
def makePsumTile (name : Var) (partitionSize freeSize : Nat) (dtype : TensorLib.Dtype) : TensorK2 :=
  {makeSbufTile name partitionSize freeSize dtype with memory := .psum}

/- Compiles a tensor-scalar operation between `src` and `imm0` that writes output to `dest`. -/
def compileTensorScalar
  (dest src : K3.TensorK3)
  (imm0 : K3.ScalarK3) (op0 : AluOp) (imm1 : K3.ScalarK3) (op1 : AluOp)
  (reverse : TensorScalarReverseOps)
  : Compile (List StatementK2) := do
  let tileDim := 4

  let srcLeadingDimensionsSize := src.type.shape.val.take (src.type.shape.ndim - 1) |> List.foldl (· * ·) 1
  let dtypeSize := dtypeSize src.type.dtype.itemsize

  let partitionSize := tileDim
  let freeSize := src.type.shape.val.getLast!
  let tileSize := partitionSize * freeSize

  if srcLeadingDimensionsSize % partitionSize != 0 then
    throw s!"compileTensorScalar: Source tensor {src.name} has a leading dimension size ({srcLeadingDimensionsSize}) that is not a multiple of the partition size {partitionSize}."

  let sourceHbmTensor ← fetch src.name
  let destHbmTensor ← fetch dest.name

  let sourceSbuf := makeSbufTile sourceHbmTensor.name partitionSize freeSize src.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name partitionSize freeSize dest.type.dtype
  let vecTileName ← gensym "vector"
  let vector := makeSbufTile vecTileName partitionSize 1 src.type.dtype

  let loopVar := "i"

  let (imm0, statements) := match imm0 with
    | .float f => (.float f, [])
    | .int n => (.int n, [])
    | .vector name _size _dtype =>
      let vecVar := "vec"
      (.var vecVar,
      [
        .load vector ⟨name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,partitionSize⟩]⟩,
        .assign vecVar (.address vecTileName)
      ])
  let imm1 ← lowerScalar imm1

  let loop := [
    StatementK2.loop loopVar 0 srcLeadingDimensionsSize partitionSize (
      [StatementK2.load sourceSbuf ⟨sourceHbmTensor.name, .expr .mult (.var loopVar) (.int (dtypeSize * freeSize)), [⟨1,tileSize⟩]⟩] ++
      statements ++
      [StatementK2.op (.tensorScalar ⟨destSbuf, sourceSbuf, imm0, op0, imm1, op1, reverse⟩)] ++
      [StatementK2.store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int (dtypeSize * freeSize)), [⟨1,tileSize⟩]⟩ destSbuf])
  ]
  pure loop

def makeSingleTensorLoop
  (srcTensor destTensor : K3.TensorK3)
  (tilePartitionSize tileFreeSize : Nat)
  (body : TensorK2 → TensorK2 → Compile (List StatementK2)) : Compile (List StatementK2) := do
  let tileSize := tilePartitionSize * tileFreeSize
  let dtypeSize := dtypeSize srcTensor.type.dtype.itemsize

  if srcTensor.type.shape.count % tileSize != 0 then
    throw s!"singletensorloop: Source tensor {srcTensor.name} has a shape ({srcTensor.type})that is not a multiple of the tile size {tileSize}."

  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let sourceSbuf := makeSbufTile sourceHbmTensor.name tilePartitionSize tileFreeSize srcTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tilePartitionSize tileFreeSize destTensor.type.dtype

  let loopVar := "i"
  let loop := [
    .loop loopVar 0 srcTensor.type.shape.count tileSize (
      [.load sourceSbuf ⟨sourceHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩] ++
      (← body destSbuf sourceSbuf) ++
      [.store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩ destSbuf])
  ]
  pure loop

def makeDoubleTensorLoop
  (aTensor bTensor destTensor : K3.TensorK3)
  (tilePartitionSize tileFreeSize : Nat)
  (body : TensorK2 → TensorK2 → TensorK2 → Compile (List StatementK2)) : Compile (List StatementK2) := do
  let tileSize := tilePartitionSize * tileFreeSize
  let destTileSize := tilePartitionSize * tileFreeSize
  let dtypeSize := dtypeSize aTensor.type.dtype.itemsize

  if aTensor.type.shape.count % tileSize != 0 then
    throw s!"singletensorloop: Source tensor {aTensor.name} has a shape ({aTensor.type})that is not a multiple of the tile size {tileSize}."

  let aHbmTensor ← fetch aTensor.name
  let bHbmTensor ← fetch bTensor.name
  let destHbmTensor ← fetch destTensor.name
  let aSbuf := makeSbufTile aHbmTensor.name tilePartitionSize tileFreeSize aTensor.type.dtype
  let bSbuf := makeSbufTile bHbmTensor.name tilePartitionSize tileFreeSize bTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name tilePartitionSize tileFreeSize destTensor.type.dtype

  let loopVar := "i"
  let loop := [
    .loop loopVar 0 aTensor.type.shape.count tileSize (
      [.load aSbuf ⟨aHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩] ++
      [.load bSbuf ⟨bHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,tileSize⟩]⟩] ++
      (← body aSbuf bSbuf destSbuf) ++
      [.store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,destTileSize⟩]⟩ destSbuf])
  ]
  pure loop

def compileTensorReduce
  (srcTensor destTensor : K3.TensorK3) (op : AluOp) (opDim : TensorSubDim) (negated : Bool) : Compile (List StatementK2) := do
  dbg_trace s!"compileTensorReduce: src={srcTensor}, dest={destTensor}, op={op}"
  let srcTensorLeadingSize := srcTensor.type.shape.val.take (srcTensor.type.shape.ndim - 1) |> List.foldl (· * ·) 1
  let srcTensorFreeSize := srcTensor.type.shape.val.getLast!
  let dtypeSize := dtypeSize srcTensor.type.dtype.itemsize

  if srcTensorLeadingSize != destTensor.type.shape.count then
    throw s!"compileTensorReduce: Source tensor {srcTensor.name} has a leading dimension size ({srcTensorLeadingSize}) that does not match the destination tensor size ({destTensor.type.shape.count})."

  let parDim := 2
  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let sourceSbuf := makeSbufTile sourceHbmTensor.name parDim srcTensorFreeSize srcTensor.type.dtype
  let destSbuf := makeSbufTile destHbmTensor.name parDim 1 destTensor.type.dtype

  let loopVar := "i"
  let loop := [
    .loop loopVar 0 srcTensorLeadingSize parDim
      [.load sourceSbuf ⟨sourceHbmTensor.name, .expr .mult (.var loopVar) (.int (dtypeSize * srcTensorFreeSize)), [⟨1,parDim * srcTensorFreeSize⟩]⟩,
      .op (.tensorReduce ⟨destSbuf, sourceSbuf, op, opDim, negated⟩),
      .store ⟨destHbmTensor.name, .expr .mult (.var loopVar) (.int dtypeSize), [⟨1,parDim⟩]⟩ destSbuf]
  ]
  pure loop

/-
Multiples a tensor of shape (B, I, J) with a tensor of shape (B, K, J) and stores the result in a tensor of shape (B, I, K).

```
# simulate np.einsum("bij,bkj->bik", a, b)
def matmul(xM,yM):
    b,i,j = xM.shape
    _,k,_ = yM.shape
    destM = np.zeros((b,i,k))
    tile = 2
    for bReg in range(b):
        x = xM[bReg]
        y = yM[bReg]
        dest = destM[bReg]
        for iReg in range(0,i,tile):
            for kReg in range(0,k,tile):
                destTile = dest[iReg:iReg+tile, kReg:kReg+tile]
                for jReg in range(0,j,tile):
                    xTile = x[iReg:iReg+tile, jReg:jReg+tile]
                    yTile = y[kReg:kReg+tile, jReg:jReg+tile]
                    destTile += xTile @ yTile.T
def matmulRaw(X,Y,tileSize=2):
    tile = tileSize
    b,i,j = X.shape
    _,k,_ = Y.shape

    X = X.reshape(-1)
    Y = Y.reshape(-1)
    DEST = np.zeros(b*i*k)
    iTiles = i//tile
    jTiles = j//tile
    kTiles = k//tile

    destStart = 0
    xStart = 0
    yStart = 0
    for bReg in range(b):
        x = xStart + bReg * i * j
        y = yStart + bReg * k * j
        dest = destStart + bReg * i * k
        for iReg in range(iTiles):
            destRow = dest + iReg * k * tile
            xRow = x + iReg * j * tile
            for kReg in range(kTiles):
                yRow = y + kReg * j * tile
                destCol = destRow + kReg * tile
                destTile = np.zeros(tile)
                for jReg in range(jTiles):
                    xCol = xRow + jReg * tile
                    yCol = yRow + jReg * tile
                    xTile = useAP(X, xCol + AP([(j,tile),(1,tile)]), tileSize)
                    yTile = useAP(Y, yCol + AP([(j,tile),(1,tile)]), tileSize)
                    destTile += tileMult(xTile, yTile)
                DEST[destCol + AP([(k,tile),(1,tile)])] = destTile
    return DEST.reshape(b, i, k)
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

  let bVar := "b"
  let iVar := "i"
  let kVar := "k"
  let jVar := "j"
  let xOffsetVar := "xOffset"
  let yOffsetVar := "yOffset"
  let destOffsetVar := "destOffset"
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

def makeCopy (destTensor srcTensor : K3.TensorK3) : Compile (List StatementK2) := do
  let sourceHbmTensor ← fetch srcTensor.name
  let destHbmTensor ← fetch destTensor.name
  let size := srcTensor.type.shape.count
  pure [.dramToDram ⟨destHbmTensor.name, .int 0, [⟨1,size⟩]⟩ ⟨sourceHbmTensor.name, .int 0, [⟨1,size⟩]⟩]

def compile120Transpose (srcTensor destTensor : K3.TensorK3) (shape : List Nat): Compile (List StatementK2) := do
  let tileDim := 2

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
def compile201Transpose (srcTensor destTensor : K3.TensorK3) (shape : List Nat): Compile (List StatementK2) := do
  let tileDim := 2

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
dims=[3, 0, 4, 1, 2]
src = <1x2000x64x1x12xf32>)
goal = <1x1x12x2000x64xf32>

-/
def compileTranspose (dst src : K3.TensorK3) (dims : List Nat) : Compile (List StatementK2) := do
  let shape := src.type.shape.val
  let goalShape := K3.permute shape dims |>.get!

  let onesBefore i := shape.take i |>.count 1
  let dimsSqueezed :=
    dims.filter (fun d => shape[d]! != 1) -- [4,1,2]
    |>.map fun d => d - onesBefore d -- [2,0,1]

  let shapeSqueezed := shape.filter (fun d => d != 1) -- [2000,64,12]
  let goalShapeSqueezed := goalShape.filter (fun d => d != 1) -- [12,2000,64]

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
    let sourceHbmTensor ← fetch src.name
    let destHbmTensor ← fetch dst.name
    let (x, y, z) := (shapeSqueezed[0]!, shapeSqueezed[1]!, shapeSqueezed[2]!)
    let (xReg, yReg, zReg) := ("x", "y", "z")
    let destAccessExpr :=
      let (aReg, bReg, cReg) := permute [xReg, yReg, zReg] dimsSqueezed |>.get! |> fun x => (x[0]!, x[1]!, x[2]!)
      let (a, b, c) := permute [x, y, z] dimsSqueezed |>.get! |> fun x => (x[0]!, x[1]!, x[2]!)
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
  --| [0, 2, 1] | [2, 1, 0] => panic! s!"No kernel for {shapeSqueezed} to goal shape {goalShapeSqueezed} ({dimsSqueezed})"
  --| [1, 0, 2] => do
  --  let (x,y,z) := (shapeSqueezed[0]!,shapeSqueezed[1]!,shapeSqueezed[2]!)
  --  let inputAp :=  [⟨y*z,x⟩,⟨z,y⟩,⟨1,z⟩]
  --  let outputAp := [⟨z,x⟩,⟨z*x,y⟩,⟨1,z⟩]
  --  pure [
  --    .dramToDram ⟨dst.name, .int 0, outputAp⟩ ⟨src.name, .int 0, inputAp⟩
  --  ]
  --| [1, 2, 0] => compile120Transpose src dst shapeSqueezed
  --| [2, 0, 1] => compile201Transpose src dst shapeSqueezed
  | _ => throw s!"Unsupported transpose shape {shapeSqueezed} to goal shape {goalShapeSqueezed}."

def compileStatement (s : K3.OperatorK3) : Compile (List StatementK2) := do
  let tileSize := 2
  let statements ← match s with
  | .activate ⟨dst, src, accumCmd, op, scale, bias, imm⟩ =>
    if accumCmd != .Idle then
      throw s!"Unsupported accumulation command {repr accumCmd} in {repr s}"
    makeSingleTensorLoop src dst tileSize tileSize fun sbufDestination sbufSource => do
      pure [
        .op (.activate ⟨sbufDestination, sbufSource, accumCmd, op, ← lowerScalar scale, ← lowerScalar bias, ← lowerScalar imm⟩),
      ]
  | .tensorTensor ⟨dst, a, b, op⟩ =>
    makeDoubleTensorLoop a b dst tileSize tileSize fun sbufA sbufB sbufDestination => do pure [
      .op (.tensorTensor ⟨sbufDestination, sbufA, sbufB, op⟩),
    ]
  | .tensorScalar ⟨dst, src, imm0, op0, imm1, op1, reverse⟩ => compileTensorScalar dst src imm0 op0 imm1 op1 reverse
  | .tensorReduce ⟨dst, src, op, opDim, negated⟩ =>
    if opDim != .X then
      throw s!"Unsupported reduction dimension {repr opDim} in {repr s}"
    compileTensorReduce src dst op opDim negated
  | .reshapeP ⟨dst, src⟩ =>
    makeSingleTensorLoop src dst tileSize tileSize fun sbufDestination sbufSource => do pure [
      .op (.copy ⟨sbufDestination, sbufSource, .none⟩),
    ]
  | .transposeP ⟨dst, src, dims⟩ => compileTranspose dst src dims
  | .matmulP ⟨dst, a, b⟩ => compileMatMul dst a b
  | .identityP ⟨dst, src⟩ => makeCopy dst src
  | _ => panic s!"compileStatement: Unsupported operator {repr s}"
  pure $ (.comment s!"{s}") :: statements

def compileProgram (f : K3.FunctionK3) : Compile ProgramK2 := do
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

def compile (f : K3.FunctionK3) : (Except String ProgramK2) × Ctx :=
  let compiled := compileProgram f
  match compiled.run default with
  | .ok ops s => (.ok ops, s)
  | .error err s => (throw err, s)
