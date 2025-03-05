/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.BIR.Compile.Memory
import KLR.BIR.Compile.Types

namespace KLR.BIR.Compile
open KLR.Core

def gatherAPs : List Expr -> Compile (List Argument)
  | [] => return []
  | x :: xs => do
    let xs <- gatherAPs xs
    match x with
    | .value (.access a) => return .PhysicalAccessPattern (<- accessToAP a) :: xs
    | _ => return xs

def compileStore (dst : Access) (e : Expr) : Compile Inst := do
  match e with
  | .value (.access _) =>
      return .TensorLoad {
        name := "load_test"  -- I think these have to be unique (need state monad?)
        ins  := <- gatherAPs [e]
        outs := <- gatherAPs [.value (.access dst)]
      }
  | .call _ args => do
      return .NoOp {
        name := "noop_test"  -- I think these have to be unique (need state monad?)
        ins  := <- gatherAPs (args.map .value)
        outs := <- gatherAPs [.value (.access dst)]
      }
  | _ => throw s!"store pattern not yet implemented {repr e}"

def compileStmt : Stmt -> Compile Inst
  | .ret _ => throw "unimp ret"
  | .store dst e => compileStore dst e
  | .assign .. => throw "unimp assign"

def compile_kernel (k : Kernel) : Compile BIR := do
  let inputs <- k.inputs.mapM (allocate .Input)
  let outputs <- k.outputs.mapM (allocate .Output)
  let internal <- k.internal.mapM (allocate .Internal)
  let allocs := inputs ++ outputs ++ internal
  let insts <- compileStmt ▷ k.body
  let insts := insts.map InstLoop.I
  -- There is alway one function with one block...
  return {
    functions := [{
      name := "sg0000"
      allocations := allocs
      blocks := [{
        name := "Block1"
        instructions := insts
        }]
    }]
  }
