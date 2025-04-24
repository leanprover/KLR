import Cli
import Gzip

open Cli

private def bytesToHex (hash : ByteArray) : String := Id.run do
  let hexChars := "0123456789abcdef".toList
  let mut result := ""
  for b in hash do
    let hi := (b >>> 4).toNat
    let lo := (b &&& 0xF).toNat
    result := result.push (hexChars[hi]!)
    result := result.push (hexChars[lo]!)
  return result

def hexCharToNibble (c : Char) : Option UInt8 :=
  let u10 : UInt8 := 10
  if '0' ≤ c && c ≤ '9' then c.toUInt8 - '0'.toUInt8
  else if 'a' ≤ c && c ≤ 'f' then c.toUInt8 - 'a'.toUInt8 + u10
  else if 'A' ≤ c && c ≤ 'F' then c.toUInt8 - 'A'.toUInt8 + u10
  else none

def hexCharToUInt8 (high : Char) (low : Char) : Option UInt8 := do
  let highNibble ← hexCharToNibble high
  let lowNibble ← hexCharToNibble low
  return (highNibble <<< 4) + lowNibble

def hexToBytes (s : String) : Option ByteArray := Id.run do
  let rec split : List Char -> List (Char × Char)
  | [] | [_] => []
  | x0 :: x1 :: xs => (x0, x1) :: split xs
  let s := if s.length % 2 == 0 then s else "0" ++ s
  let mut buf := ByteArray.mkEmpty (s.length / 2)
  for (lo, hi) in split s.data do
    match hexCharToUInt8 hi lo with
    | none => return none
    | some n => buf := buf.push n
  return buf

def runGzip (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let bytes <- IO.FS.readBinFile input
  IO.println s!"Got (hex) bytes: {bytesToHex bytes}"
  if p.hasFlag "file" then
    let file := p.flag! "file" |>.as! String
    let bytes' := Util.gzip bytes
    IO.FS.writeBinFile file bytes'
    IO.println s!"Wrote {file}"
  else
    let bytes' := Util.gzip bytes
    IO.eprintln s!"Compressed {bytes.size} bytes to {bytes'.size}"
    IO.println s!"Zipped (hex) bytes: {bytesToHex bytes'}"
  return 0

def gzipCmd : Cmd := `[Cli|
  gzip VIA runGzip; ["0.0.1"]
  "Gzip input stream"

  FLAGS:
    f, file : String ; "write to gz file (default is stdout)"

  ARGS:
    input : String ; "input bytes as hex"
]

def main (args : List String) : IO UInt32 :=
  if args.isEmpty then do
    IO.println gzipCmd.help
    return 0
  else do
   gzipCmd.validate args
