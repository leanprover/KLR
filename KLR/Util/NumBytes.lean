/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import TensorLib.Common
import Util.Enum

namespace KLR.Util

open Lean(Command Expr InductiveVal Name Term getEnv isInductive mkIdent)
open Lean.Elab(registerDerivingHandler)
open Lean.Elab.Command(CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Deriving(Context Header mkContext mkHeader mkInstanceCmds)
open Lean.Elab.Term(TermElabM)
open TensorLib(impossible)

class NumBytes (a : Type) where
  numBytes : a -> Nat

export NumBytes(numBytes)

namespace NumBytes

instance : NumBytes Int8 where
  numBytes _ := 1

instance : NumBytes UInt8 where
  numBytes _ := 1

instance : NumBytes Int16 where
  numBytes _ := 2

instance : NumBytes UInt16 where
  numBytes _ := 2

instance : NumBytes Int32 where
  numBytes _ := 4

instance : NumBytes UInt32 where
  numBytes _ := 4

instance : NumBytes UInt64 where
  numBytes _ := 8

instance : NumBytes Int64 where
  numBytes _ := 8

instance : NumBytes Float32 where
  numBytes _ := 4

instance : NumBytes Float where
  numBytes _ := 8

instance : NumBytes (BitVec n) where
  numBytes _ := (n + 7) / 8

instance [NumBytes a][NumBytes b] : NumBytes (a × b) where
  numBytes := fun (x, y) => numBytes x + numBytes y

instance [Enum a] : NumBytes a where
  numBytes _ := 1

end NumBytes

def mkNumBytesHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``NumBytes 1 indVal

def mkNumBytesBody (header : Header) (e : Expr): TermElabM Term := do
  let indName := e.getAppFn.constName!
  let env <- getEnv
  let fields := Lean.getStructureFieldsFlattened env indName (includeSubobjectFields := false)
  let target := mkIdent header.targetNames[0]!
  let apps : Array Term <- fields.mapM fun f => ``(NumBytes.numBytes ($target).$(mkIdent f))
  let body : Term <- `(Array.sum #[ $apps,* ])
  return body

def mkNumBytesFunction (ctx : Context) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[0]!
  let header     ←  mkNumBytesHeader ctx.typeInfos[0]!
  let binders    := header.binders
  let type       ← Lean.Elab.Term.elabTerm header.targetType none
  let body   ← mkNumBytesBody header type
  `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Nat := $body:term)

private def mkNumBytesInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "NumBytes" declName
  let cmds := #[← mkNumBytesFunction ctx] ++ (← mkInstanceCmds ctx ``NumBytes #[declName])
  return cmds

private def errMsg := "deriving NumBytes only works on single structures"

def mkNumBytesInstanceHandler (declNames : Array Name) : CommandElabM Bool := match declNames with
| #[] => impossible "Expected a type"
| #[t] => do
  if (Lean.isStructure (<- getEnv) t) && (<- Lean.getConstInfoInduct t).all.length == 1 then
    let cmds ← liftTermElabM <| mkNumBytesInstance t
    cmds.forM elabCommand
    return true
  else
    throwError errMsg
    return false
| _ => throwError errMsg

initialize
  registerDerivingHandler ``NumBytes mkNumBytesInstanceHandler

end KLR.Util
