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

import KLR.Core.Basic
namespace KLR.Core

/-- Algebraic representation of an affine function taking Int^dim to Int -/
structure Layout (dim : Nat) where
  offset  : Nat
  steps : List Int
  nums    : List Nat
  offsets : List Nat
  steps_dim : steps.length = dim
  nums_dim : nums.length = dim
  deriving Repr

def TensorName.toAP (a : TensorName) : KLR.Err AccessPattern := do
  let layout := a.shape.toList
  let steps := layout.tail ++ [1]
  let steps := steps.scanr (· * ·) 1 |>.dropLast
  return {
    tensor := a
    parNum := layout[0]!
    pattern := (List.zip steps layout).map (fun (step, size) => ⟨step, size, 0⟩)
    freeOffset := 0
  }

private def getTensorName (shape : List Nat) : Err TensorName :=
  let addr : Address := {
    name := "A", memory := .sbuf,
    parSize := 4, freeSize := 24,
    parOffset := none, freeOffset := none
  }
  let t := TensorName.make "A" .int8 (.mk shape.head! shape.tail!) addr
  match t with
  | .ok t => .ok t
  | .error err => .error err

#guard (do
  let t <- getTensorName [4,3,2]
  let ac <- TensorName.toAP t
  let bir := BirAccessPattern.fromAccessPattern ac
  .ok (bir.pattern, bir.offset)) == .ok ([⟨6,4,0⟩, ⟨2,3,0⟩, ⟨1,2,0⟩], 0)

#guard (do
  let t <- getTensorName [4,3]
  let ac <- TensorName.toAP t
  let bir := BirAccessPattern.fromAccessPattern ac
  .ok (bir.pattern, bir.offset)) == .ok ([⟨3,4,0⟩, ⟨1,3,0⟩], 0)


-- Returns a tuple of (step, cnt, fixed)
-- Where step is the size of the step
-- cnt is number elements inside the step
-- fixed speicifies if the dimension been fixed by taking an index
def AccessBasic.idx_sz_and_offset (idxs : List Index) : List (Int × Int × Bool) :=
  idxs.map (fun idx =>
      match idx with
      | .coord c => (1, c, true)
      | .slice s => (((s.u - s.l) / s.step), min s.l s.u, false))

def idxToAp (layout : List Nat) (idxs : List Index) : (List APPair) × (List Nat) :=
  let steps := layout.tail ++ [1] -- step for dim 0 is 1 and the rest is prev dim
  let steps := steps.scanr (· * ·) 1 |>.dropLast -- actual step is accum of all prev step sizes
  let sz_off := AccessBasic.idx_sz_and_offset idxs -- get all index size and offset
  let pairs : List APPair := List.zipWith (fun s (cnt, off, _fixed) => ⟨s, cnt.toNat, off.toNat⟩) steps sz_off
  -- fixed should be a list of offsets where 3rd element of sz_off is true
  let fixed := sz_off.mapIdx (fun i (_, _, isFixed) => if isFixed then some i else none) |>.filterMap id
  (pairs, fixed)

def AccessBasic.toAP (a : AccessBasic) : KLR.Err AccessPattern := do
  let layout := a.tensor.shape.toList
  let (pairs, fixed) := idxToAp layout a.indexes
  return {
    tensor := a.tensor
    parNum := pairs[0]!.num
    pattern := pairs
    freeOffset := (pairs.map (fun x => x.offset)).sum
    fixedAxis := fixed
  }

private def testAccess (idxs : List Index) : KLR.Err (List APPair × Nat) := do
  let addr : Address := {
    name := "A", memory := .sbuf,
    parSize := 4, freeSize := 24,
    parOffset := none, freeOffset := none
  }
  let t <- TensorName.make "A" .int8 (.mk 4 [3, 2]) addr
  let ac <- AccessBasic.make t idxs
  match AccessBasic.toAP ac with
  | .ok ac =>
    let bir := BirAccessPattern.fromAccessPattern ac
    .ok (bir.pattern, bir.offset)
  | .error e => .error e

#guard testAccess
 [.coord 0, .coord 0, .coord 0] ==
  .ok ([⟨6,1,0⟩, ⟨2,1,0⟩, ⟨1,1,0⟩], 0)
#guard testAccess
 [.coord 0, .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)] ==
  .ok ([⟨6,1,0⟩, ⟨2,3,0⟩, ⟨1,2,0⟩], 0)
#guard testAccess
 [.coord 1, .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)] ==
  .ok ([⟨6,1,1⟩, ⟨2,3,0⟩, ⟨1,2,0⟩], 6)
#guard testAccess
 [.slice (Slice.make! 1 3 1), .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,2,1⟩, ⟨2,3,0⟩, ⟨1,2,0⟩], 6)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .coord 0, .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,4,0⟩, ⟨2,1,0⟩, ⟨1,2,0⟩], 0)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .coord 1, .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,4,0⟩, ⟨2,1,1⟩, ⟨1,2,0⟩], 2)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .slice (Slice.make! 1 3 1), .slice (Slice.make! 0 2 1)] ==
 .ok ([⟨6,4,0⟩, ⟨2,2,1⟩, ⟨1,2,0⟩], 2)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .slice (Slice.make! 0 3 1), .coord 0] ==
 .ok ([⟨6,4,0⟩, ⟨2,3,0⟩, ⟨1,1,0⟩], 0)
#guard testAccess
 [.slice (Slice.make! 0 4 1), .slice (Slice.make! 0 3 1), .coord 1] ==
 .ok ([⟨6,4,0⟩, ⟨2,3,0⟩, ⟨1,1,1⟩], 1)

def AccessPattern.toAP (a : AccessPattern) : KLR.Err AccessPattern :=
  .ok a

def Access.toAP (a : Access) : KLR.Err AccessPattern :=
  match a with
  | .simple s => TensorName.toAP s
  | .basic b => AccessBasic.toAP b
  | .pattern p => .ok p
  | .birPattern _ => throw "Converting birAP to AP is lossy"

structure FixedPairs where
  pairs: List APPair
  fixedAxis: List Nat

def Access.combineAP (a : Access) (pat: FixedPairs) : KLR.Err AccessPattern := do
  let ap <- Access.toAP a
  let pat1 := ap.pattern
  let pairs := List.zipWith (fun p1 p2 => APPair.combine p1 p2) pat1 pat.pairs
  return {
    tensor := ap.tensor
    parNum := pairs[0]!.num
    pattern := pairs
    freeOffset := pairs.foldl (fun acc p => acc + p.tensor_offset.toNat) 0
    fixedAxis := pat.fixedAxis
  }

-- Normalize one AP in terms of the other. This is needed to resolve the fixed axis of one AP
-- in terms of it's right axeses.
--  E.g: in pattern `[1:3, 0, 1:3][1:2, 1:2]` the dimmension 1 is fixed and we will need to insert
-- additional dimension when normalizing second access to align on dimmensions
-- so second access `[(3,2), (1,2)]` becomes `[(3,2),(N, 1),(1,2)]` where N is the size of fixed
-- dimmension from parent AP. We don't have to use N. But that would require special casing the
-- combine operator for that stub value
def Access.normWithAP (this: FixedPairs) (inTerms : FixedPairs) : FixedPairs :=
  let (rvPairs, _, newFixedAxis) := inTerms.pairs.foldlIdx (fun i (acc, thisIdx, fixedAxis) pair =>
    if inTerms.fixedAxis.contains i then
      (acc ++ [APPair.mk pair.step 1 0], thisIdx, fixedAxis ++ [i])
    else
      let shiftedThisFixed := if this.fixedAxis.contains thisIdx then
        let shift := (inTerms.fixedAxis.filter (· < i)).length
        fixedAxis ++ [i]
      else fixedAxis
      (acc ++ [this.pairs[thisIdx]!], thisIdx + 1, shiftedThisFixed)
  ) ([], 0, [])
  FixedPairs.mk rvPairs newFixedAxis

def Access.combine (a : Access) (idx : List Index) : KLR.Err AccessPattern := do
  for i in idx do
    match i with
    -- This is probably artificial. We need to test combine better with stride != 1
    -- until this check can be dropped
    | .slice s =>
      if s.step != 1 then
        throw "can't combine indecies with stride != 1"
    | _ => pure ()
  let ap <- Access.toAP a
  let shape := <- a.shape
  let (pat2, fixed2) := idxToAp shape.toList idx
  let normResult := Access.normWithAP ⟨pat2, fixed2⟩ ⟨ap.pattern, ap.fixedAxis⟩
  let rv <- Access.combineAP a normResult
  .ok rv


private def testAccess2 (idxs1 : List Index) (idxs2 : List Index) : KLR.Err (List APPair × Nat) := do
  let addr : Address := {
    name := "A", memory := .sbuf,
    parSize := 4, freeSize := 24,
    parOffset := none, freeOffset := none
  }
  let t <- TensorName.make "A" .int8 (.mk 4 [3, 2]) addr
  let ab <- AccessBasic.make t idxs1
  let ac <- AccessBasic.toAP ab
  let ac2 <- Access.combine (.pattern ac) idxs2
  let bir := BirAccessPattern.fromAccessPattern ac2
  .ok (bir.pattern, bir.offset)

#guard testAccess2
    [.slice (Slice.make! 1 2 1), .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)]
    [.coord 0, .slice (Slice.make! 0 3 1), .coord 0] ==
    .ok ([⟨6,1,1⟩, ⟨2,3,0⟩, ⟨1,1,0⟩], 6)
#guard testAccess2
    [.slice (Slice.make! 1 2 1), .slice (Slice.make! 0 3 1), .slice (Slice.make! 0 2 1)]
    [.coord 0, .slice (Slice.make! 1 2 1), .slice (Slice.make! 0 2 1)] ==
    .ok ([⟨6,1,1⟩, ⟨2,1,1⟩, ⟨1,2,0⟩], 8)
#guard testAccess2
    [.slice (Slice.make! 1 3 1), .slice (Slice.make! 1 3 1), .slice (Slice.make! 0 2 1)]
    [.slice (Slice.make! 0 2 1), .slice (Slice.make! 1 2 1), .coord 1] ==
     .ok ([⟨6,2,1⟩, ⟨2,1,2⟩, ⟨1,1,1⟩], 11)
#guard testAccess2
    [.slice (Slice.make! 1 3 1), .slice (Slice.make! 1 3 1), .coord 1]
    [.slice (Slice.make! 0 2 1), .slice (Slice.make! 1 2 1)] ==
     .ok ([⟨6,2,1⟩, ⟨2,1,2⟩, ⟨1,1,1⟩], 11)
#guard testAccess2
    [.slice (Slice.make! 1 3 1), .slice (Slice.make! 1 3 1), .coord 1]
    [.slice (Slice.make! 0 2 1), .coord 1] ==
     .ok ([⟨6,2,1⟩, ⟨2,1,2⟩, ⟨1,1,1⟩], 11)
#guard testAccess2
    [.coord 1, .slice (Slice.make! 1 3 1), .slice (Slice.make! 0 2 1)]
    [.coord 1, .slice (Slice.make! 0 2 1)] ==
     .ok ([⟨6,1,1⟩, ⟨2,1,2⟩, ⟨1,2,0⟩], 10)

end KLR.Core
