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
    | .tensor _ | .access _ _ => return .PhysicalAccessPattern (<- accessToAP x) :: xs
    | _ => return xs

def compileStore (t : TensorName) (ix : List Index) (e : Expr) : Compile Inst := do
  match e with
  | .tensor _ | .access _ _ => do
      return .TensorLoad {
        name := "load_test"  -- I think these have to be unique (need state monad?)
        ins  := <- gatherAPs [.access (.tensor t) ix]
        outs := <- gatherAPs [e]
      }
  | .call (.operator _) args [] => do
      return .NoOp {
        name := "noop_test"  -- I think these have to be unique (need state monad?)
        ins  := <- gatherAPs [.access (.tensor t) ix]
        outs := <- gatherAPs args
      }
  | _ => throw s!"store pattern not yet implemented {repr e}"

def compileStmt : Stmt -> Compile Inst
  | .ret _ => throw "unimp ret"
  | .store t ix e => compileStore t ix e
  | .assign .. => throw "unimp assign"
  | .loop .. => throw "unimp loop"

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
