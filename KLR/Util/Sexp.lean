/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin

This is copied and modified from FromToJson.lean in the Lean sources. The biggest difference is
supporting both positional and named arguments.
-/
import TensorLib
import Util.Float
import Util.Hex

open Lean(Command ConstructorVal CoreM Expr Ident InductiveVal Macro Name Syntax TSyntax Term getConstInfoCtor getConstInfoInduct getEnv getStructureFieldsFlattened isInductive isStructure mkIdent quote)
open Lean.Core(mkFreshUserName)
open Lean.Elab(registerDerivingHandler)
open Lean.Elab.Command(CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Deriving(Context Header mkContext mkDiscrs mkHeader mkInductiveApp mkInstanceCmds mkLet mkLocalInstanceLetDecls)
open Lean.Elab.Term(TermElabM elabBinders elabTerm)
open Lean.Meta(forallTelescopeReducing mkListLit)
open Lean.Parser.Term(bracketedBinderF doExpr matchAlt matchAltExpr)
open Lean.PrettyPrinter(ppCommand)
open TensorLib(Err impossible toLEByteArray)

namespace KLR.Util

inductive Sexp where
| atom (s : String)
| list (es : List Sexp)
deriving BEq, Inhabited, Repr

namespace Sexp

def lispString : Sexp -> String
| atom s => s
| list es =>
  let body := " ".intercalate (es.map lispString)
  s!"({body})"

#guard lispString (list [atom "a", atom "b", list [atom "c"]]) == "(a b (c))"

instance : ToString Sexp where
  toString := lispString

end Sexp

class ToSexp (a : Type) where
  toSexp : a -> Sexp

export ToSexp(toSexp)

namespace Sexp

instance : ToSexp String where
  toSexp n := atom n

instance : ToSexp Bool where
  toSexp | true => atom "true"
         | false => atom "false"

instance : ToSexp Int where
  toSexp n := atom (toString n)

instance : ToSexp Nat where
  toSexp n := toSexp (Int.ofNat n)

instance : ToSexp Float32 where
  toSexp f := atom f.toString

instance : ToSexp Float where
  toSexp f := atom f.toString

instance [ToSexp a] : ToSexp (List a) where
  toSexp e := list (e.map toSexp)

instance [ToSexp a] : ToSexp (Array a) where
  toSexp e := toSexp e.toList

instance [ToSexp a] [ToSexp b] : ToSexp (a × b) where
  toSexp p := list [toSexp p.1, toSexp p.2]

instance [ToSexp a] : ToSexp (Option a) where
  toSexp
  | none => list []
  | some x => list [toSexp x]

instance [BEq a][Hashable a][ToSexp a][ToSexp b] : ToSexp (Std.HashMap a b) where
  toSexp n := toSexp n.toList

instance : ToSexp ByteArray where
  toSexp arr := .atom (Hex.encode arr)

instance : ToSexp (BitVec n) where
  toSexp vec := toSexp (toLEByteArray vec)

instance : ToSexp UInt8 where
  toSexp n := toSexp n.toNat

instance : ToSexp UInt16 where
  toSexp n := toSexp n.toNat

instance : ToSexp UInt32 where
  toSexp n := toSexp n.toNat

instance : ToSexp UInt64 where
  toSexp n := toSexp n.toNat

instance : ToSexp Int8 where
  toSexp n := toSexp n.toInt

instance : ToSexp Int16 where
  toSexp n := toSexp n.toInt

instance : ToSexp Int32 where
  toSexp n := toSexp n.toInt

instance : ToSexp Int64 where
  toSexp n := toSexp n.toInt

end Sexp

class FromSexp (a : Type) where
  fromSexp? : Sexp -> Err a

export FromSexp(fromSexp?)

namespace Sexp

instance : FromSexp String where
  fromSexp? s := do match s with
  | atom a => return a
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Bool where
  fromSexp? s := do match s with
  | atom "true" => return true
  | atom "false" => return false
  | atom a => throw s!"Can't parse {a} as an Bool"
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Int where
  fromSexp? s := do match s with
  | atom a => match a.toInt? with
    | some n => return n
    | none => throw s!"Can't parse {a} as an Int"
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Nat where
  fromSexp? s := do
    let n <- @fromSexp? Int _ s
    return n.toNat

instance : FromSexp Float32 where
  fromSexp?
  | atom s => return parseFloat32 s
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Float where
  fromSexp?
  | atom s => return parseFloat s
  | list _ => throw "Expected Atom, got List"

instance [FromSexp a] : FromSexp (List a) where
  fromSexp?
  | atom a => throw s!"can't parse list from atom: {a}"
  | list es => es.mapM (@fromSexp? a _)

instance [FromSexp a] : FromSexp (Array a) where
  fromSexp? e := (@fromSexp? (List a) _ e).map fun a => a.toArray

instance [FromSexp a] [FromSexp b] : FromSexp (a × b) where
  fromSexp? s := match s with
  | atom a => throw s!"Can't parse pair from atom: {a}"
  | list [x, y] => do
    let n <- fromSexp? x
    let m <- fromSexp? y
    return (n, m)
  | xs => throw s!"Can't parse pair from non pair list: {xs}"

instance [FromSexp a] : FromSexp (Option a) where
  fromSexp?
  | atom a => throw s!"Can't parse option from atom: {a}"
  | list [] => return none
  | list [x] => return some (<- fromSexp? x)
  | l => throw s!"Can't parse option from non-singleton list: {l}"

instance [BEq a][Hashable a][FromSexp a][FromSexp b] : FromSexp (Std.HashMap a b) where
  fromSexp? s := do return Std.HashMap.ofList (<- fromSexp? s)

instance [BEq a][Hashable a][ToSexp a][ToSexp b] : ToSexp (Std.HashMap a b) where
  toSexp n := toSexp n.toList

instance : FromSexp ByteArray where
  fromSexp?
  | .atom s => liftM (Hex.decode s)
  | .list _ => throw "not a hex-encoded byte array"

instance : FromSexp (BitVec n) where
  fromSexp? s := do
    let arr <- @fromSexp? ByteArray _ s
    return arr.toBitVecLE n

instance : FromSexp UInt8 where
  fromSexp? s := do
    let n <- @fromSexp? Nat _ s
    return n.toUInt8

instance : FromSexp UInt16 where
  fromSexp? s := do
    let n <- @fromSexp? Nat _ s
    return n.toUInt16

instance : FromSexp UInt32 where
  fromSexp? s := do
    let n <- @fromSexp? Nat _ s
    return n.toUInt32

instance : FromSexp UInt64 where
  fromSexp? s := do
    let n <- @fromSexp? Nat _ s
    return n.toUInt64

instance : FromSexp Int8 where
  fromSexp? s := do
    let n <- @fromSexp? Int _ s
    return n.toInt8

instance : FromSexp Int16 where
  fromSexp? s := do
    let n <- @fromSexp? Int _ s
    return n.toInt16

instance : FromSexp Int32 where
  fromSexp? s := do
    let n <- @fromSexp? Int _ s
    return n.toInt32

instance : FromSexp Int64 where
  fromSexp? s := do
    let n <- @fromSexp? Int _ s
    return n.toInt64

def length? : Sexp -> Err Nat
| atom _ => throw "calling length on atom"
| list es => return es.length

def tail : Sexp -> Err Sexp
| list (_ :: xs) => return list xs
| _ => throw "tail"

-- For lists of the form ((x1 E1) (x2 E2) ...), getValue xi --> Ei
def assocRaw (sexp : Sexp) (x : String) : Option Sexp := match sexp with
| list (list [atom y, e] :: rest) => if x == y then e else (list rest).assocRaw x
| list (_ :: rest) => (list rest).assocRaw x
| _ => none

def assoc (a : Type) [FromSexp a] (sexp : Sexp) (x : String) : Err a :=
  match sexp.assocRaw x with
  | none => throw "Can't find field: {x}"
  | some e => fromSexp? e

def assocWithDefault (a : Type) [FromSexp a] (sexp : Sexp) (x : String) (default : a) : Err a :=
  match sexp.assocRaw x with
  | none => return default
  | some e => fromSexp? e

def getIndexRaw (sexp : Sexp) (n : Nat) : Err Sexp :=
  match sexp, n with
  | atom _, _ => throw "Can't getIndex of an atom"
  | list [], _ => throw "Not enough elements of sexp"
  | list (x :: _), 0 => return x
  | list (_ :: xs), n => getIndexRaw (list xs) (n - 1)

def getIndex (a : Type) [FromSexp a] (sexp : Sexp) (n : Nat) : Err a := do
  let v <- sexp.getIndexRaw n
  fromSexp? v

def hasTag (sexp : Sexp) (tag : String) : Bool := match sexp with
| list (atom tag' :: _) => tag == tag'
| _ => false

private def mkToSexpHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``ToSexp 1 indVal

private def mkFromSexpHeader (indVal : InductiveVal) : TermElabM Header := do
  let header ← mkHeader ``FromSexp 0 indVal
  let sexpArg ← `(bracketedBinderF|(sexp : Sexp))
  return {header with
    binders := header.binders.push sexpArg}

private def mkSexpField (n : Name) : CoreM Term := do
  let .str .anonymous s := n | throwError "invalid sexp field name {n}"
  return Syntax.mkStrLit s

private def mkToSexpBodyForStruct (header : Header) (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let fields ← fields.mapM fun field => do
    let nm ← mkSexpField field
    let target := mkIdent header.targetNames[0]!
    ``(list [atom $nm, toSexp ($target).$(mkIdent field)])
  `(list <| [$fields,*])

private def mkToSexpBodyForInduct (ctx : Context) (header : Header) (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let toSexpFuncId := mkIdent ctx.auxFunNames[0]!
  -- Return syntax to sexp-ify `id`, either via `ToSexp` or recursively
  -- if `id`'s type is the type we're deriving for.
  let mkToSexp (id : Ident) (type : Expr) : TermElabM Term := do
    if type.isAppOf indVal.name then `($toSexpFuncId:ident $id:ident)
    else ``(toSexp $id:ident)
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal fun ctor args userNames => do
    let ctorStr := ctor.name.eraseMacroScopes.getString!
    match args, userNames with
    | #[], _ => ``(toSexp $(quote ctorStr))
    | #[(x, t)], none => ``(list [atom $(quote ctorStr), $(← mkToSexp x t)])
    | xs, none =>
      let xs ← xs.mapM fun (x, t) => mkToSexp x t
      ``(list [atom $(quote ctorStr), $[$xs:term],*])
    | xs, some userNames =>
      let xs ← xs.mapIdxM fun idx (x, t) => do
        `(list [ atom $(quote userNames[idx]!.eraseMacroScopes.getString!), $(← mkToSexp x t) ])
      ``(list [atom $(quote ctorStr), $[$xs:term],*])
  `(match $[$discrs],* with $alts:matchAlt*)

where
  mkAlts
    (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term): TermElabM (Array (TSyntax ``matchAlt)) := do
      let mut alts := #[]
      for ctorName in indVal.ctors do
        let ctorInfo ← getConstInfoCtor ctorName
        let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
          let mut patterns := #[]
          -- add `_` pattern for indices
          for _ in [:indVal.numIndices] do
            patterns := patterns.push (← `(_))
          let mut ctorArgs := #[]
          -- add `_` for inductive parameters, they are inaccessible
          for _ in [:indVal.numParams] do
            ctorArgs := ctorArgs.push (← `(_))
          -- bound constructor arguments and their types
          let mut binders := #[]
          let mut userNames := #[]
          for i in [:ctorInfo.numFields] do
            let x := xs[indVal.numParams + i]!
            let localDecl ← x.fvarId!.getDecl
            if !localDecl.userName.hasMacroScopes then
              userNames := userNames.push localDecl.userName
            let a := mkIdent (← mkFreshUserName `a)
            binders := binders.push (a, localDecl.type)
            ctorArgs := ctorArgs.push a
          patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
          let rhs ← rhs ctorInfo binders (if userNames.size == binders.size then some userNames else none)
          `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
        alts := alts.push alt
      return alts

private def mkFromSexpBodyForStruct (indName : Name) : TermElabM Term := do
  let env <- getEnv
  let fields := getStructureFieldsFlattened env indName (includeSubobjectFields := false)
  -- Handle named arguments
  let getNamed ← fields.mapM (fun field => do
    let default : TermElabM (Option Term) := match Lean.getDefaultFnForField? env indName field with
    | none => return none
    | some default => do
      let constInfo ← Lean.getConstInfoDefn default
      let v := constInfo.value
      let syn <- Lean.PrettyPrinter.delab v
      some syn
    let default <- default
    let getter ← match default with
    | none => `(assoc _ sexp $(← mkSexpField field))
    | some default => `(assocWithDefault _ sexp $(← mkSexpField field) $(default))
    let getter ← `(doElem| Except.mapError (fun s => (toString $(quote indName)) ++ "." ++ (toString $(quote field)) ++ ": " ++ s) <| $getter)
    return getter
  )
  -- Handle positional arguments
  let getPositional <- fields.mapIdxM (fun i field => do
      let getter ← `(getIndex _ sexp $(Syntax.mkNatLit i))
      let getter ← `(doElem| Except.mapError (fun s => (toString $(quote indName)) ++ "." ++ (toString $(quote field)) ++ ": " ++ s) <| $getter)
      return getter
  )
  let fields := fields.map mkIdent
  `(do
      let n <- sexp.length?
      if $(Syntax.mkNatLit fields.size) < n then throw "length mismatch for struct" else
      try
        $[let $fields:ident ← $getNamed]*
        return { $[$fields:ident := $(id fields)],* }
      catch _ =>
        $[let $fields:ident ← $getPositional]*
        return { $[$fields:ident := $(id fields)],* }
  )

/-
Generating code for inductives is complicated by the fact that only some of the
fields need be named, and that there is a tag we need to match. TagArgInfo and TagArg
are used to simplify the logic
-/
structure TagArgInfo where
  ident : Ident
  type : Expr
  username : Option Name
  default : Option Term
  index : Nat
deriving Inhabited

namespace TagArgInfo

def nameToStringTerm (name : Name) : Term := Syntax.mkStrLit name.getString!

-- Captures 'sexp'
def rhsNamed (info : TagArgInfo) : TermElabM Term := match info.username, info.default with
| some k, none => `(
  <- sexp.assoc _ $(nameToStringTerm k)
)
| some k, some d => `(
  <- sexp.assocWithDefault _ $(nameToStringTerm k) $(d)
)
| _, _ => impossible "invariant violation"

-- Captures 'sexp'
def rhsIndex (info : TagArgInfo) : TermElabM Term := `(
  <- (<- sexp.tail).getIndex _ $(Syntax.mkNumLit (toString info.index)):num
)

end TagArgInfo

structure TagInfo where
  ctorName : Name
  arr : Array TagArgInfo

namespace TagInfo

def usernameCount (tagInfo : TagInfo) : Nat := Id.run do
  let mut n := 0
  for i in [0:tagInfo.arr.size] do
    if tagInfo.arr[i]!.username.isSome then n := n + 1
  return n

-- Use this to compare to the sexp atom appearing first in the list
def ctorString (tagInfo : TagInfo) : String := tagInfo.ctorName.eraseMacroScopes.getString!

def ctorIdent (tagInfo : TagInfo) : Ident := mkIdent tagInfo.ctorName

def isNamed (tagInfo : TagInfo) : Bool := tagInfo.arr.all fun info => info.username.isSome

def isEnum (tagInfo : TagInfo) : Bool := tagInfo.arr.size == 0

def tag (tagInfo : TagInfo) : Term := quote tagInfo.ctorString

-- Captures the name `sexp`
def toSyntax (tagInfo : TagInfo) : TermElabM Term :=
  if tagInfo.isEnum then `(
    match sexp with
    | .atom s => if s == $(tagInfo.tag) then return $(tagInfo.ctorIdent):ident else throw s!"incorrect tag"
    | _ => Except.error s!"incorrect tagged union: {sexp}"
  ) else if tagInfo.isNamed then do
      let rhssNamed : Array Term <- tagInfo.arr.mapM fun info => info.rhsNamed
      let rhssIndex : Array Term <- tagInfo.arr.mapM fun info => info.rhsIndex
      `(if sexp.hasTag $(tagInfo.tag) then do
          try return $(tagInfo.ctorIdent):ident $rhssNamed* catch _ => return $(tagInfo.ctorIdent):ident $rhssIndex*
        else throw s!"incorrect tag")

    else do
      let rhss : Array Term <- tagInfo.arr.mapM fun info => info.rhsIndex
      `(if sexp.hasTag $(tagInfo.tag) then do return $(tagInfo.ctorIdent):ident $rhss* else throw s!"incorrect tag")

end TagInfo

private def mkFromSexpBodyForInduct (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let alts ← mkAlts indVal
  let auxTerm ← alts.foldrM (fun xs x => `(Except.orElseLazy $xs (fun _ => $x))) (← `(Except.error "no inductive constructor matched"))
  `($auxTerm)
where
  mkAlts (indVal : InductiveVal) : TermElabM (Array Term) := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let n := ctorInfo.numFields
    let alt ← do forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut infos : Array TagArgInfo := #[]
      let mut binders   := #[]
      let mut userNames := #[]
      for i in [:n] do
        let x := xs[indVal.numParams + i]!
        let localDecl ← x.fvarId!.getDecl
        let default <- match localDecl.type.getOptParamDefault? with
        | none => pure none
        | some d => do
          let c <- Lean.PrettyPrinter.delab d
          pure (some c)
        let username := if !localDecl.userName.hasMacroScopes then some localDecl.userName else none
        match username with
        | some name => userNames := userNames.push name
        | none => pure ()
        let a := mkIdent (← mkFreshUserName `a)
        binders := binders.push (a, localDecl.type)
        infos := infos.push (TagArgInfo.mk a localDecl.type username default i)
      let tagInfo := TagInfo.mk ctorName infos
      let stx ← tagInfo.toSyntax
      pure (stx, ctorInfo.numFields)
    alts := alts.push alt
  -- the smaller cases, especially the ones without fields are likely faster
  let alts' := alts.qsort (fun (_, x) (_, y) => x < y)
  return alts'.map Prod.fst

private def mkToSexpBody (ctx : Context) (header : Header) (e : Expr): TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    mkToSexpBodyForStruct header indName
  else
    mkToSexpBodyForInduct ctx header indName

private def mkToSexpAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let header     ←  mkToSexpHeader ctx.typeInfos[i]!
  let binders    := header.binders
  elabBinders binders fun _ => do
  let type       ← elabTerm header.targetType none
  let mut body   ← mkToSexpBody ctx header type
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``ToSexp header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Sexp := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Sexp := $body:term)

private def mkFromSexpBody (e : Expr) : TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    mkFromSexpBodyForStruct indName
  else
    mkFromSexpBodyForInduct indName

private def mkFromSexpAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indval     := ctx.typeInfos[i]!
  let header     ←  mkFromSexpHeader indval --TODO fix header info
  let binders    := header.binders
  elabBinders binders fun _ => do
  let type ← elabTerm header.targetType none
  let mut body ← mkFromSexpBody type
  if ctx.usePartial || indval.isRec then
    let letDecls ← mkLocalInstanceLetDecls ctx ``FromSexp header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Except String $(← mkInductiveApp ctx.typeInfos[i]! header.argNames) := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Except String $(← mkInductiveApp ctx.typeInfos[i]! header.argNames) := $body:term)

private def mkToSexpMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkToSexpAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkFromSexpMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkFromSexpAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkToSexpInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "toSexp" declName
  let cmds := #[← mkToSexpMutualBlock ctx] ++ (← mkInstanceCmds ctx ``ToSexp #[declName])
  return cmds

private def mkFromSexpInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "fromSexp?" declName
  let cmds := #[← mkFromSexpMutualBlock ctx] ++ (← mkInstanceCmds ctx ``FromSexp #[declName])
  return cmds

-- TODO: These instance handlers are generating |mutual types| full mutual definitions, which
-- is n^2 code. Paul found a simpler way in Serde/Elab, but it's not yet clear if this seemingyl
-- excessive generation, which uses a different Context in each one, is necessary for corner
-- cases. If it turns out to be unnecessary, we'll switch to the Serde method.
private def mkToSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkToSexpInstance declName
      for cmd in cmds do
        -- SM: Leave this in
        -- dbg_trace (<- liftTermElabM <| ppCommand cmd)
        elabCommand cmd
    return true
  else
    throwError "Generation of ToSexp failed"
    return false

private def mkFromSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkFromSexpInstance declName
      for cmd in cmds do
        -- SM: Leave this in
        -- dbg_trace (<- liftTermElabM <| ppCommand cmd)
        elabCommand cmd
    return true
  else
    throwError "Generation of FromSexp failed"
    return false

initialize
  registerDerivingHandler ``ToSexp mkToSexpInstanceHandler
  registerDerivingHandler ``FromSexp mkFromSexpInstanceHandler

declare_syntax_cat sexp (behavior := symbol)
syntax ident : sexp
syntax str : sexp
syntax "-"? num : sexp
syntax "-"? scientific : sexp
syntax "(" sexp* ")" : sexp
syntax "sexp% " sexp : term

macro_rules
  | `(sexp% $k:ident)       => `(atom $(Syntax.mkStrLit k.getId.getString!))
  | `(sexp% $n:str)         => `(atom $n)
  | `(sexp% $n:num)         => `(atom (toString $n))
  | `(sexp% $n:scientific)  => `(atom (toString $n))
  | `(sexp% -$n:num)        => `(atom (toString (-$n)))
  | `(sexp% -$n:scientific) => `(atom (toString (-$n)))
  | `(sexp% ( $[$xs]* ) )   => `(list [ $[sexp% $xs],* ])
  | `(sexp% $stx)           =>
    if stx.raw.isAntiquot then
      let stx := ⟨stx.raw.getAntiquotTerm⟩
      `(toSexp $stx)
    else
      Macro.throwUnsupported
