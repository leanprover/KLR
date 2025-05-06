/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import Archive
import Cli

open Cli
open KLR.Util.Archive
open System(FilePath)

def create (p : Parsed) : IO UInt32 := do
  let files := p.variableArgsAs! String
  let outfile := p.flag! "output" |>.as! String
  let mut entries := []
  for file in files do
    if <- FilePath.pathExists file then
      let contents <- IO.FS.readBinFile file
      let entry := ArchiveEntry.mk file contents
      entries := entry :: entries
    else
      IO.eprintln s!"File doesn't exist: {file}"
      return 1
  let tarBytes := createTar entries
  IO.FS.writeBinFile outfile tarBytes
  IO.println s!"Wrote tar archive to {outfile} ({tarBytes.size} bytes)"
  return 0

def cwd : IO FilePath := IO.FS.realPath "."

def extract (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let tarBytes <- IO.FS.readBinFile input
  let entries := extractTar tarBytes
  IO.println s!"Extracted {entries.length} files from archive:"
  let dir <-
    if p.hasFlag "dir" then
      pure $ FilePath.mk (p.flag! "dir" |>.as! String)
    else
      cwd
  for entry in entries do
    IO.println s!"File: {entry.filename}"
    let path := System.FilePath.join dir entry.filename
    match System.FilePath.parent path with
    | some parent => IO.FS.createDirAll parent
    | none => pure ()
    IO.FS.writeBinFile path entry.content
    IO.println s!"  Extracted to {path}"
  return 0

def createCmd : Cmd := `[Cli|
  create VIA create; ["0.0.1"]
  "Create a tar archive from files"

  FLAGS:
    o, output : String; "output tar file"

  ARGS:
    ...files : String; "input file paths"
]

def extractCmd : Cmd := `[Cli|
  extract VIA extract; ["0.0.1"]
  "Extract files from a tar archive"

  FLAGS:
    C, dir : String; "directory to extract files to (default is cwd)"

  ARGS:
    input : String; "input tar file"
]

def archiveCmd : Cmd := `[Cli|
  archive VIA (fun _ => pure 0); ["0.0.1"]
  "Work with tar archives"

  SUBCOMMANDS:
    createCmd;
    extractCmd
]

def main (args : List String) : IO UInt32 :=
  if args.isEmpty then do
    IO.println archiveCmd.help
    return 0
  else
    archiveCmd.validate args
