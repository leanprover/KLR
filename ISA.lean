/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import ISA.Basic
import ISA.Generator
import ISA.Parser
import ISA.Simplify

namespace ISA

/-
This code is incomplete. For development it is useful to focus
on a single instruction format. However, you will also need the
common definitions, e.g. to output the s3d3_ts format for version 3:

# lake exe isagen v3/common.json v3/s3d3_ts.json
-/

def parseISAFiles (args : List String) : IO Unit := do
  let mut files : Array Parser.ISAFile := #[]
  for arg in args do
    let str <- IO.FS.readFile arg
    let json <- Lean.Json.parse str
    let items : List Parser.ParseItem <- Lean.fromJson? json
    files := files.push { name := arg, items }
  for file in files do
    IO.println s!"{file.name} {file.items.length} items found"
  IO.println "\n--Translating AST..."
  let isa <- Parser.translate 0 files
  --for (n,s) in isa.opcodes do
  --  IO.println s!"{n} => {s}"
  IO.println "\n--Simplifying AST..."
  let isa <- Simplify.simplify isa
  --for (n,s) in isa.insts do
  --  IO.println s!"{n} => {s}"
  --for (n,b) in isa.opcodes do
  --  IO.println s!"{n} => {b}"
  IO.println "\n--Generating AST..."
  Generate.generate isa
