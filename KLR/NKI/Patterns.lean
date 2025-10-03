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

import KLR.Compile.Pass
import KLR.NKI.Basic
import KLR.Util

/-
Simplify Patterns found in let statements.

This module will rewrite complex patterns into simple patterns.
For example, the following:

  let x, y, z = e

will be transformed to:

  let tmp = e
  let x = tmp[0]
  let y = tmp[1]
  let x = tmp[2]
-/

namespace KLR.NKI
open Compile.Pass

-- Simplify Pattern = Simpat
abbrev Simpat := Pass Unit

-- Build a simple subscript expression, e.g. v[2,3,1]
private def subscript (v : Name) (ix : List Int) : Expr :=
  let pos : Pos := { line := 0 }
  let ix := ix.map fun n => .coord ⟨.value (.int n), pos ⟩
  let e' := .access ⟨ .var v, pos ⟩ ix
  ⟨ e', pos ⟩

/-
Expand a complex pattern into a set of subscript expressions.

  ((x,y),z) = v

becomes

  x = v[0][0]
  y = v[0][1]
  x = v[1]
-/
private def expand (v : Name) (ix : List Int) (i : Int) (ps : List Pattern) : List Stmt' :=
  match ps with
  | [] => []
  | p :: ps =>
    let l := match p with
      | .var n => [.letM (.var n) none (subscript v (ix ++ [i]))]
      | .tuple ps => expand v (ix ++ [i]) 0 ps
    l ++ expand v ix (i+1) ps

section Testing

private def extract : Stmt' -> List Int
  | .letM _ _ ⟨.access _ ix, _⟩ => ix.map fun
    | .coord ⟨.value (.int i), _⟩ => i
    | _ => panic! "invalid"
  | _ => panic! "invalid"

private def test (ps : List Pattern) : List (List Int) :=
  let l := expand `x [] 0 ps
  l.map extract

private def p1 : List Pattern :=
  [.tuple [.var `a, .var `b], .tuple [.var `c], .var `d]

private def p2 : List Pattern :=
  [.var `a, .var `b, .var `c, .var `d]

private def p3 : List Pattern :=
  [.tuple [.tuple [.var `a]]]

#guard test p1 == [[0,0], [0,1], [1,0], [2]]
#guard test p2 == [[0], [1], [2], [3]]
#guard test p3 == [[0,0,0]]

end Testing

mutual
private def stmt (s : Stmt) : Simpat (List Stmt) :=
  withPos s.pos do
    let l <- stmt' s.stmt
    let l := l.map fun s' => ⟨ s', s.pos ⟩
    return l
  termination_by sizeOf s
  decreasing_by cases s; simp; omega

private def stmts (l : List Stmt) : Simpat (List Stmt) := do
  l.flatMapM stmt
  termination_by sizeOf l

private def stmt' (s : Stmt') : Simpat (List Stmt') := do
  match s with
  | .expr ..
  | .assert ..
  | .ret ..
  | .declare ..
  | .setM ..
  | .breakLoop
  | .continueLoop
  | .letM (.var ..) .. => return [s]
  | .letM (.tuple []) .. => throw "internal errro: empty tuple pattern not allowed in let binding"
  | .letM (.tuple [.var n]) ty e => return [.letM (.var n) ty e]
  | .letM (.tuple ps) ty e => do
      let x <- freshName
      let st : Stmt' := .letM (.var x) ty e
      return st :: expand x [] 0 ps
  | .ifStm c t e => return [.ifStm c (<- stmts t) (<- stmts e)]
  | .forLoop x iter body => return [.forLoop x iter (<- stmts body)]
  | .whileLoop test body => return [.whileLoop test (<- stmts body)]
  | .dynWhile t body => return [.dynWhile t (<- stmts body)]
  termination_by sizeOf s
end

private def func (f : Fun) : Simpat Fun :=
  return { f with body := <- stmts f.body }

def simplifyPatterns (k : Kernel) : Simpat Kernel := do
  return { k with funs := <- k.funs.mapM func }
