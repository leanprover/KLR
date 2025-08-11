import KLR.TGR.AST
import Lean
import TensorLib.Tensor
import KLR.TGRKLR.Operators

namespace KLR.TGRKLR.K3

open KLR.TGR(TensorTy)

abbrev Var := String

structure TensorK3 where
  name : Var
  shape : TensorTy
deriving Inhabited, Repr, BEq

inductive ScalarK3
  | float (f : Float32)
  | int (f : Nat)
  | vector (name : Var) (size : Nat) (dtype : TensorLib.Dtype)
deriving Inhabited, Repr, BEq

abbrev OperatorK3 := KLR.TGRKLR.Operator TensorK3 ScalarK3

structure FunctionK3 where
  name : String
  inputs : List TensorK3
  outputs : List TensorK3
  statements : List OperatorK3

instance : ToString TensorK3 where
  toString t :=
    s!"%{t.name}<{t.shape.shape.val.toString}>"

instance : ToString ScalarK3 where
  toString
    | .float f => s!"{f}"
    | .int i => s!"{i}"
    | .vector name size dtype=> s!"{name}<{size}x{dtype}>"

instance : ToString FunctionK3 where
  toString f :=
    let inputs := f.inputs.map ToString.toString |> ",".intercalate
    let outputs := f.outputs.map ToString.toString |> ",".intercalate
    let body := f.statements.map ToString.toString |> "\n\t".intercalate
    s!"def {f.name}({inputs}) -> {outputs} :\n\t{body}"
