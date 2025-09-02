import KLR.TGR.AST
import KLR.K.Operators
import Lean
import TensorLib.Tensor

namespace KLR.K.K3

open KLR.TGR(TensorTy)

abbrev Var := String

/- A tensor in K3 has a name, shape, and datatype -/
structure TensorK3 where
  name : Var
  type : TensorTy
deriving Inhabited, Repr, BEq

/- A scalar in K3 can be a float, int, or vector, where a vector is a named
variable with a size and datatype. -/
inductive ScalarK3
  | float (f : Float32)
  | int (f : Nat)
  | vector (name : Var) (size : Nat) (dtype : TensorLib.Dtype)
deriving Inhabited, Repr, BEq

abbrev OperatorK3 := KLR.K.Operator TensorK3 ScalarK3

/- K3 functions take a list of arguments as input and have a list of outputs.
The input arguments can be referred to by name, and it is assumed that by the
end of the instruction stream the named output tensors will have been written to. -/
structure FunctionK3 where
  name : String
  inputs : List TensorK3
  outputs : List TensorK3
  statements : List OperatorK3
deriving Inhabited, Repr, BEq

instance : ToString TensorK3 where
  toString t :=
    s!"%{t.name}<{t.type.shape.val.toString}>"

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
