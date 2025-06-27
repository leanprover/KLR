import KLR.HLR.AST

namespace KLR.HLR

def constFold (f : Function) : Function := Id.run do
  let mut source := f.statements |>.reverse
  let mut newStatements := []
  for s in source do
    match s with
    | .assign v _ ty =>
      let deps := transitiveDependencies f v
      let hasNonConstDeps := deps.any (fun dep =>
        match findVar f dep with
        | .some (.arg _) => true
        | _ => false)
      if hasNonConstDeps then
        newStatements := s :: newStatements
      else
        -- remove the source statements that depend on this variable
        source := source.filter (fun x => match x with
          | .assign v' _ _ => ! deps.contains v'
          | _ => true)
        -- replace the variable with a constant
        newStatements :=
          (.assign v (.const (.denseElements []) ty.shape ty.dtype) ty) :: newStatements -- TODO: replace with the actual constant value
    | _ => newStatements := s :: newStatements
  return {f with statements := newStatements.reverse }


end KLR.HLR
