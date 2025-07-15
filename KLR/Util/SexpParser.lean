/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Util.Common
import Util.Sexp

open KLR(get!)
open Lean(FileMap)
open Std.Internal.Parsec(many many1 many1Chars peek? peek! satisfy)
open Std.Internal.Parsec.String(Parser pchar skipChar)

namespace KLR.Util.Sexp.Parse

-- For debugging
private def remaining [ToString α] (p : Parser α) (s : String) : String := match p s.mkIterator with
 | .success it v => s!"success: {v}: {it.remainingToString}"
 | .error it msg => s!"error: {msg}: {it.remainingToString}"

def comment : Parser Unit :=
  skipChar ';' <* many (satisfy fun c => c != '\n')

-- There is probably a better way to do this
partial def space : Parser Unit := fun it =>
  if it.atEnd then .success it ()
  else if it.curr == ';' then
    match comment it with
    | .success it _ => space it
    | .error it msg => .error it msg
  else if it.curr.isWhitespace then space it.next
  else .success it ()

def atomChar : Parser Char :=
  satisfy fun c => !c.isWhitespace && c != '(' && c != ')' && c != ';'

def string : Parser String := many1Chars atomChar
def atom : Parser Sexp := Functor.map Sexp.atom string

-- Parse space up to a sexp
partial def sexp : Parser Sexp :=
  atom <|> list
 where
  list' := skipChar '(' *> space *> many (sexp <* space) <* skipChar ')'
  list := Functor.map (fun arr => Sexp.list arr.toList) list'

def defaultFilename : String := "<input>"

def fromString' (p : Parser α) (s : String) (filename : String := defaultFilename) : Err α := do
  let filemap := FileMap.ofString s
  match p s.mkIterator with
  | .success it v =>
    if it.remainingBytes == 0 then return v else throw s!"Remaining input: {it.remainingToString}"
  | .error it msg =>
    let pos := filemap.toPosition it.pos
    throw s!"{filename}:{pos.line}:{pos.column}: {msg}"

def fromString (s : String) (filename : String := defaultFilename) : Err Sexp :=
  fromString' (space *> sexp <* space) s filename

def fromString! (s : String) (filename : String := defaultFilename) : Sexp :=
  get! $ fromString s filename

def listFromString (s : String) (filename : String := defaultFilename) : Except String (List Sexp) :=
  let p := Functor.map Array.toList (many1 (space *> sexp <* space))
  fromString' p s filename

def listFromString! (s : String) (filename : String := defaultFilename) : List Sexp :=
  get! $ listFromString s filename

def fromFile (file : String) : IO Sexp := do
  fromString (<- IO.FS.readFile file) file

def listFromFile (filepath : String) : IO (List Sexp) := do
  listFromString (<- IO.FS.readFile filepath) filepath

#guard fromString! "hello" == sexp%hello
#guard fromString! "hello " == sexp%hello
#guard fromString! " hello" == sexp%hello
#guard fromString! "()" == sexp%()
#guard fromString! "(hello world)" == sexp%(hello world)
#guard fromString! "(🏎️ 🏎️ 🏎️ 🏎️)" == sexp%("🏎️" "🏎️" "🏎️" "🏎️")
#guard fromString! "(hello world)   " == sexp%(hello world)
#guard fromString! "(a (b c) d)" == sexp% (a (b c) d)
#guard fromString! "(hello world) ; trailing comment" == sexp%(hello world)
#guard fromString! "  \t\n  (  a   b  \t c  )  \n  " == sexp% (a b c)
#guard fromString! "hello-world" == sexp% "hello-world"
#guard fromString! "a.b.c" == sexp% "a.b.c"
#guard fromString! "(((((a)))))" == sexp% (((((a)))))
#guard listFromString! "(first list) atom (second list)" == [sexp% (first list), sexp% atom, sexp% (second list)]
#guard listFromString! "atom1 (list item) atom2" == [sexp% atom1, sexp% (list item), sexp% atom2]
#guard fromString! "(a b c)   " == sexp% (a b c)
#guard listFromString! "first ;\nsecond" == [sexp% first, sexp% second]
#guard listFromString! "first ; comment  \n second" == [sexp% first, sexp% second]
#guard fromString! "(hello ; this is a comment\n world)" == sexp%(hello world)
#guard listFromString! "first ;\nsecond" == [sexp% first, sexp% second]
#guard listFromString! "first ; comment\nsecond ; another comment\n(third fourth)" == [sexp% first, sexp% second, sexp%(third fourth)]
#guard fromString! "(define (factorial n) ; recursive factorial function\n  (if (= n 0) ; base case\n      1\n      (* n (factorial (- n 1)))))" == sexp%(define (factorial n) ("if" ("=" n 0) 1 ("*" n (factorial ("-" n 1)))))

end KLR.Util.Sexp.Parse
