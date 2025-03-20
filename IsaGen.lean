/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import ISA

def main (args : List String) : IO UInt32 := do
  ISA.parseISAFiles args
  return 0
