/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Util.Common
import Util.Sexp

open KLR(get!)

namespace KLR.Util.Sexp.Parse

structure ParsingState where
  iter : String.Iterator
  line : Nat
  col : Nat
  file : String
  deriving Repr, Inhabited, Nonempty

namespace ParsingState

def init (s : String) (file : String := "<input>") : ParsingState := {
  iter := String.mkIterator s
  line := 1
  col := 0
  file
}

def rest (s : ParsingState) : String := s.iter.remainingToString

def done? (s : ParsingState) : Bool := s.iter.atEnd

end ParsingState

abbrev PState := StM ParsingState

def raise (msg : String) : PState a := do
  let st ← get
  throw s!"{st.file}:{st.line}:{st.col}: {msg}"

def done? : PState Bool := return (<- get).done?

def peek : PState Char := do
  if <- done? then raise "peeking at empty string" else
  return (<- get).iter.curr

def lookingAt' (p : Char -> Bool) : PState Bool := do
  if <- done? then raise "lookingAt empty string"
  return p (<- peek)

def lookingAt (c : Char) : PState Bool := lookingAt' fun c' => c == c'

def pop : PState Char := do
  if <- done? then raise "popping empty string"
  let s <- get
  let c := s.iter.curr
  let iter := s.iter.next
  let line := if c == '\n' then s.line + 1 else s.line
  let col := if c == '\n' then 0 else s.col + 1
  set { s with iter, line, col }
  return c

def pop' : PState Unit := do
  let _ <- pop

def skipSemicolonComment : PState Unit := do
  let c <- pop
  if c != ';' then raise "not at a ;"
  repeat do
    if <- done? then break
    let c <- pop
    if c == '\n' then break

def skip : PState Unit := do
  repeat do
    if <- done? then break
    let c <- peek
    if c.isWhitespace then pop'
    else if c == ';' then skipSemicolonComment
    else break

def consumeChar (c : Char) : PState Unit := do
  let c' <- pop
  if c != c' then raise s!"expected {c} got {c'}"

def isAtomChar (c : Char) : Bool := !c.isWhitespace && c != ';' && c != '(' && c != ')'

def parseAtom : PState String := do
  let mut token := ""
  let mut started := false
  repeat do
    if <- done? then break
    let c <- peek
    if !(isAtomChar c) then break
    if !started then
      started := true
    token := token.push c
    pop'
  if !started then raise "Couldn't find an atom"
  return token

mutual
partial def parseSexp : PState Sexp := do
  skip
  if <- done? then raise "expected s-expression"
  let c <- peek
  match c with
  | '(' => do
    pop'
    let sexps <- parseSexpList
    consumeChar ')'
    return .list sexps
  | ')' => raise "unexpected ')'"
  | _ =>
    let a <- parseAtom
    return Sexp.atom a

partial def parseSexpList : PState (List Sexp) := do
  let mut sexps := []
  repeat do
    skip
    if <- (done? <||> lookingAt ')') then break
    sexps := (<- parseSexp) :: sexps
  return sexps.reverse
end

def parseMany : PState (List Sexp) := do
  let mut sexps := []
  while !(<- done?) do
    let s <- parseSexp
    sexps := s :: sexps
    skip
  return sexps.reverse

def defaultFilename : String := "<input>"

def parseListFromString (s : String) (file : String := defaultFilename) : Except String (List Sexp) :=
  let state := ParsingState.init s file
  match parseMany.run state with
  | .ok sexps state =>
    match skip.run state with
    | .ok _ state => if state.done? then return sexps else throw s!"Unexpected input after {state.line}, column {state.col}: "
    | .error msg _ => throw msg
  | .error msg _ => throw msg

def parseSexpFromString (input : String) (file : String := defaultFilename) : Err Sexp := do
  match <- parseListFromString input file with
  | [s] => return s
  | [] => throw "No sexps"
  | _ :: _ => throw "Found multiple sexps"

def parseSexpFromFile (file : String) : IO Sexp := do
  parseSexpFromString (<- IO.FS.readFile file) file

def parseListFromFile (filepath : String) : IO (List Sexp) := do
  parseListFromString (<- IO.FS.readFile filepath) filepath

#guard parseSexpFromString "hello" == .ok (sexp%hello)
#guard parseSexpFromString "(hello world)" == .ok (sexp%(hello world))
#guard parseSexpFromString "(🏎️ 🏎️ 🏎️ 🏎️)" == .ok (sexp%("🏎️" "🏎️" "🏎️" "🏎️"))
#guard parseSexpFromString "(hello world)   " == .ok (sexp%(hello world))
#guard parseSexpFromString "(hello world) ; trailing comment" == .ok (sexp%(hello world))
#guard parseSexpFromString "(a (b c) d)" == .ok (sexp% (a (b c) d))
#guard parseSexpFromString "(hello ; this is a comment\n world)" == .ok (sexp%(hello world))
#guard parseListFromString "atom1 (list item) atom2" == .ok [sexp% atom1, sexp% (list item), sexp% atom2]
#guard parseListFromString "first ;\nsecond" == .ok [sexp% first, sexp% second]
#guard parseListFromString "first ; comment\nsecond ; another comment\n(third fourth)" == .ok [sexp% first, sexp% second, sexp%(third fourth)]
#guard parseSexpFromString "hello" == .ok (sexp% hello)
#guard parseSexpFromString "(a b c)" == .ok (sexp% (a b c))
#guard parseSexpFromString "(a (b c) d)" == .ok (sexp% (a (b c) d))
#guard parseSexpFromString "(hello ; this is a comment\n world)" == .ok (sexp% (hello world))
#guard parseListFromString "atom1 (list item) atom2" == .ok [sexp% atom1, sexp% (list item), sexp% atom2]
#guard parseListFromString "first ; comment\nsecond ; another comment\n(third fourth)" == .ok [sexp% first, sexp% second, sexp% (third fourth)]
#guard parseSexpFromString "()" == .ok (sexp% ())
#guard match parseSexpFromString "(" with | .error _ => true | .ok _ => false
#guard parseSexpFromString "  \t\n  (  a   b  \t c  )  \n  " == .ok (sexp% (a b c))
#guard parseSexpFromString "(a b c)   " == .ok (sexp% (a b c))
#guard parseSexpFromString "atom   " == .ok (sexp% atom)
#guard parseListFromString "first ;\nsecond" == .ok [sexp% first, sexp% second]
#guard parseListFromString "first ; comment\nsecond" == .ok [sexp% first, sexp% second]
#guard get! (parseSexpFromString "(define (factorial n) ; recursive factorial function\n  (if (= n 0) ; base case\n      1\n      (* n (factorial (- n 1)))))")
   == sexp%(define (factorial n) ("if" ("=" n 0) 1 ("*" n (factorial ("-" n 1)))))
#guard match parseSexpFromString ")" with | .error _ => true | .ok _ => false
#guard match parseSexpFromString "(a b" with | .error _ => true | .ok _ => false
#guard match parseSexpFromString "" with | .error _ => true | .ok _ => false
#guard parseSexpFromString "hello-world" == .ok (sexp% "hello-world")
#guard parseSexpFromString "test123" == .ok (sexp% test123)
#guard parseSexpFromString "a.b.c" == .ok (sexp% "a.b.c")
#guard parseSexpFromString "(((((a)))))" == .ok (sexp% (((((a))))))
#guard parseListFromString "(first list) atom (second list)" == .ok [sexp% (first list), sexp% atom, sexp% (second list)]

end KLR.Util.Sexp.Parse
