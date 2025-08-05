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

-- import KLR.NKI.Typed.Common
-- import KLR.NKI.Typed.Python
-- import KLR.NKI.Typed.TIR

import Lean
open Lean Parser

instance : Insert (Name × Parser × Nat) (TokenMap (Parser × Nat)) where
  insert | (n, p, prec), tm => tm.insert n (p, prec)
instance : Singleton (Name × Parser × Nat) (TokenMap (Parser × Nat)) where
  singleton | (n, p, prec) => TokenMap.insert {} n (p, prec)

inductive BinOp
  | pow | mul | div | mod | add | sub
  | land | lor

inductive Exp
  | nat (n : Nat)
  | bool (b : Bool)
  | binOp (op : BinOp) (x y : Exp)

unsafe def pExp : Parser :=
  p
where
  tt   := leading_parser:maxPrec "True"
  ff   := leading_parser:maxPrec "False"
  num  := Parser.numLit
  pow  := trailing_parser:100:101 " ** " >> p 100
  mul  := trailing_parser:90:90 " * " >> p 91
  div  := trailing_parser:90:90 " / " >> p 91
  mod  := trailing_parser:90:90 " % " >> p 91
  add  := trailing_parser:85:85 " + " >> p 86
  sub  := trailing_parser:85:85 " - " >> p 86
  land := trailing_parser:75:75 " and " >> p 76
  lor  := trailing_parser:70:70 " or " >> p 71

  parsingTables := {
    leadingTable := {
      (`True, tt, maxPrec),
      (`False, ff, maxPrec),
      (numLitKind, num, maxPrec)
    },
    trailingTable := {
      (`«**», pow, 100),
      (`«*», mul, 90),
      (`«/», div, 90),
      (`«%», mod, 90),
      (`«+», add, 85),
      (`«-», sub, 85),
      (`and, land, 75),
      (`or, lor, 70)
    },
  }
  pFn :=
    prattParser `exp parsingTables .default (mkAntiquot "exp" `exp false true).fn
  p (prec : Nat := 0) :=
    {fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn `exp pFn)}

partial def eExp : TSyntax `exp → Except String Exp
  | `(pExp.tt| True) => .ok <| .bool true
  | `(pExp.ff| False) => .ok <| .bool false
  | `(pExp.num| $n:num) => .ok <| .nat n.getNat
  | `(pExp| $x:exp * $y:exp) => do .ok (.binOp .mul (← eExp x) (← eExp y))
  | `(pExp| $x:exp / $y:exp) => do .ok (.binOp .div (← eExp x) (← eExp y))
  | `(pExp| $x:exp % $y:exp) => do .ok (.binOp .mod (← eExp x) (← eExp y))
  | `(pExp| $x:exp + $y:exp) => do .ok (.binOp .add (← eExp x) (← eExp y))
  | `(pExp| $x:exp - $y:exp) => do .ok (.binOp .sub (← eExp x) (← eExp y))
  /- These don't work -/
  -- | `(pExp| $b:exp ** $e:exp) => do .ok (.binOp .pow (← eExp b) (← eExp e))
  -- | `(pExp| $x:exp and $y:exp) => do .ok (.binOp .land (← eExp x) (← eExp y))
  -- | `(pExp| $x:exp or $y:exp) => do .ok (.binOp .or (← eExp x) (← eExp y))
  | _ => throw "unsupported"
