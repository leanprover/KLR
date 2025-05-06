import Cli
import Gzip
import Util.Base64

open Cli
open KLR.Util.Gzip(gzip gunzip)
open KLR.Util.Base64(encode)

def runGzip (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let bytes <- IO.FS.readBinFile input
  IO.println s!"Got (base64) bytes: {encode bytes}"
  if p.hasFlag "file" then
    let file := p.flag! "file" |>.as! String
    let bytes' := gzip bytes
    IO.FS.writeBinFile file bytes'
    IO.println s!"Wrote {file}"
  else
    let bytes' := gzip bytes
    IO.eprintln s!"Compressed {bytes.size} bytes to {bytes'.size}"
    IO.println s!"Zipped (base64) bytes: {encode bytes'}"
  return 0

def runGunzip (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let bytes <- IO.FS.readBinFile input
  IO.println s!"Got compressed (base64) bytes: {encode bytes}"
  if p.hasFlag "file" then
    let file := p.flag! "file" |>.as! String
    let bytes' := gunzip bytes
    IO.FS.writeBinFile file bytes'
    IO.println s!"Wrote decompressed data to {file}"
  else
    let bytes' := gunzip bytes
    IO.eprintln s!"Decompressed {bytes.size} bytes to {bytes'.size}"
    IO.println s!"Unzipped (base64) bytes: {encode bytes'}"
  return 0

def gzipCmd : Cmd := `[Cli|
  gzip VIA runGzip; ["0.0.1"]
  "Gzip input stream"

  FLAGS:
    f, file : String ; "write to gz file (default is stdout)"

  ARGS:
    input : String ; "input file"
]

def gunzipCmd : Cmd := `[Cli|
  gunzip VIA runGunzip; ["0.0.1"]
  "Gunzip compressed stream"

  FLAGS:
    f, file : String ; "write decompressed data to file (default is stdout)"

  ARGS:
    input : String ; "input compressed file"
]

def mainCmd : Cmd := `[Cli|
  gzutil NOOP; ["0.0.1"]
  "Gzip utility functions"

  SUBCOMMANDS:
    gzipCmd;
    gunzipCmd
]

def main (args : List String) : IO UInt32 :=
  if args.isEmpty then do
    IO.println mainCmd.help
    return 0
  else do
   mainCmd.validate args
