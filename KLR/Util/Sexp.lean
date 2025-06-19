/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin

This is copied and modified from FromToJson.lean in the Lean sources. The biggest difference is
supporting both positional and named arguments.
-/
import TensorLib

open Lean(Command ConstructorVal CoreM Expr Ident InductiveVal Macro Name Syntax TSyntax Term getConstInfoCtor getConstInfoInduct getEnv getStructureFieldsFlattened isInductive isStructure mkIdent quote)
open Lean.Core(mkFreshUserName)
open Lean.Elab(registerDerivingHandler)
open Lean.Elab.Command(CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Deriving(Context Header mkContext mkDiscrs mkHeader mkInductiveApp mkInstanceCmds mkLet mkLocalInstanceLetDecls)
open Lean.Elab.Term(TermElabM elabBinders elabTerm)
open Lean.Meta(forallTelescopeReducing mkListLit)
open Lean.Parser.Term(bracketedBinderF doExpr matchAlt matchAltExpr)
open Lean.PrettyPrinter(ppCommand)
open TensorLib(Err impossible)

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

class ToSexp (a : Type) where
  toSexp : a -> Sexp

export ToSexp(toSexp)

instance : ToSexp String where
  toSexp n := atom n

instance : ToSexp Int where
  toSexp n := atom (toString n)

instance : ToSexp Nat where
  toSexp n := toSexp (Int.ofNat n)

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

class FromSexp (a : Type) where
  fromSexp : Sexp -> Err a

def fromSexp (a : Type) [FromSexp a] (e : Sexp) : Err a :=
  FromSexp.fromSexp e

instance : FromSexp String where
  fromSexp s := do match s with
  | atom a => return a
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Int where
  fromSexp s := do match s with
  | atom a => match a.toInt? with
    | some n => return n
    | none => throw s!"Can't parse {a} as an Int"
  | list _ => throw "Expected Atom, got List"

instance : FromSexp Nat where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toNat

instance [FromSexp a] : FromSexp (List a) where
  fromSexp
  | atom a => throw s!"can't parse list from atom: {a}"
  | list es => es.mapM (fromSexp a)

instance [FromSexp a] : FromSexp (Array a) where
  fromSexp e := (fromSexp (List a) e).map fun a => a.toArray

instance [FromSexp a] [FromSexp b] : FromSexp (a × b) where
  fromSexp s := match s with
  | atom a => throw s!"Can't parse pair from atom: {a}"
  | list [x, y] => do
    let n <- fromSexp _ x
    let m <- fromSexp _ y
    return (n, m)
  | xs => throw s!"Can't parse pair from non pair list: {xs}"

instance [FromSexp a] : FromSexp (Option a) where
  fromSexp
  | atom a => throw s!"Can't parse option from atom: {a}"
  | list [] => return none
  | list [x] => return some (<- fromSexp a x)
  | l => throw s!"Can't parse option from non-singleton list: {l}"

instance : FromSexp UInt8 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt8

instance : FromSexp UInt16 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt16

instance : FromSexp UInt32 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt32

instance : FromSexp UInt64 where
  fromSexp s := do
    let n <- fromSexp Nat s
    return n.toUInt64

instance : FromSexp Int8 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt8

instance : FromSexp Int16 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt16

instance : FromSexp Int32 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt32

instance : FromSexp Int64 where
  fromSexp s := do
    let n <- fromSexp Int s
    return n.toInt64

def length? : Sexp -> Err Nat
| atom _ => throw "calling length on atom"
| list es => return es.length

-- For lists of the form ((x1 E1) (x2 E2) ...), getValue xi --> Ei
private def assocRaw (sexp : Sexp) (x : String) : Option Sexp := match sexp with
| list (list [atom y, e] :: rest) => if x == y then e else (list rest).assocRaw x
| list (_ :: rest) => (list rest).assocRaw x
| _ => none

private def assoc (a : Type) [FromSexp a] (sexp : Sexp) (x : String) : Err a :=
  match sexp.assocRaw x with
  | none => throw "Can't find field: {x}"
  | some e => fromSexp a e

private def getIndexRaw (sexp : Sexp) (n : Nat) : Err Sexp :=
  match sexp, n with
  | atom _, _ => throw "Can't getIndex of an atom"
  | list [], _ => throw "Not enough elements of sexp"
  | list (x :: _), 0 => return x
  | list (_ :: xs), n => getIndexRaw (list xs) (n - 1)

private def getIndex (a : Type) [FromSexp a] (sexp : Sexp) (n : Nat) : Err a := do
  let v <- sexp.getIndexRaw n
  fromSexp a v

-- Parses a sexp-encoded `structure` or `inductive` constructor. Used mostly by `deriving FromSexp`.
private def parseTaggedAux
    (sexp : Sexp)
    (tag : String)
    (nFields : Nat)
    (fieldNames? : Option (Array Name)) : Except String (Array Sexp) :=
  if nFields == 0 then
    match sexp with
    | .atom s => if s == tag then Except.ok #[] else throw s!"incorrect tag: {s} ≟ {tag}"
    | _ => Except.error s!"incorrect tagged union: {sexp}"
  else
    match fieldNames? with
    | some fieldNames =>
      do
        let mut fields := #[]
        for fieldName in fieldNames do
          fields := fields.push (← sexp.assocRaw fieldName.getString!)
        Except.ok fields
    | none => match sexp with
      | list (atom tag' :: fields) =>
        if tag == tag' then
          if fields.length == nFields then
            Except.ok fields.toArray
          else
            Except.error s!"incorrect number of fields: {fields.length} ≟ {nFields}"
        else
          Except.error s!"tag mismatch: {tag} ≟ {tag'}"
      | _ =>
        Except.error s!"Expected structure/inductive sexp"

/-
`tag` is the name of the constructor, that becomes the first element of the sexp list. For example, in

    inductive Foo where
    | a (x : Nat)

we'd get a Sexp representation of (a (x 5)) where "a" is the "tag".
-/
private def parseTagged
    (sexp : Sexp)
    (tag : String)
    (nFields : Nat)
    (fieldNames? : Option (Array Name)) : Except String (Array Sexp) := do
  try
    parseTaggedAux sexp tag nFields fieldNames?
  catch exn => match fieldNames? with
    | none => throw exn
    | _ => parseTaggedAux sexp tag nFields none -- Maybe the caller used the non-named syntax for an inductive with names

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
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let getters1 ← fields.mapM (fun field => do
    let getter ← `(assoc _ sexp $(← mkSexpField field))
    let getter ← `(doElem| Except.mapError (fun s => (toString $(quote indName)) ++ "." ++ (toString $(quote field)) ++ ": " ++ s) <| $getter)
    return getter
  )
  let getters2 <- fields.mapIdxM (fun i field => do
      let getter ← `(getIndex _ sexp $(Syntax.mkNatLit i))
      let getter ← `(doElem| Except.mapError (fun s => (toString $(quote indName)) ++ "." ++ (toString $(quote field)) ++ ": " ++ s) <| $getter)
      return getter
  )
  let fields := fields.map mkIdent
  `(do
      let n <- sexp.length?
      if n != $(Syntax.mkNatLit fields.size) then throw "length mismatch for struct" else
      try
        $[let $fields:ident ← $getters1]*
        return { $[$fields:ident := $(id fields)],* }
      catch _ =>
        $[let $fields:ident ← $getters2]*
        return { $[$fields:ident := $(id fields)],* }
  )

private def mkFromSexpBodyForInduct (ctx : Context) (indName : Name) : TermElabM Term := do
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
        let mut binders   := #[]
        let mut userNames := #[]
        for i in [:n] do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)
        let fromSexpFuncId := mkIdent ctx.auxFunNames[0]!
        -- Return syntax to parse `id`, either via `FromSexp` or recursively
        -- if `id`'s type is the type we're deriving for.
        -- NB: this captures the `sexps` variable, declared below.
        let mkFromSexp (idx : Nat) (type : Expr) : TermElabM (TSyntax ``doExpr) :=
          if type.isAppOf indVal.name then `(doExpr| $fromSexpFuncId:ident sexps[$(quote idx)]!)
          else `(doExpr| fromSexp _ sexps[$(quote idx)]!)
        let identNames := binders.map Prod.fst
        let fromSexps ← binders.mapIdxM fun idx (_, type) => mkFromSexp idx type
        let userNamesOpt ← if binders.size == userNames.size then
          ``(some #[$[$(userNames.map quote)],*])
        else
          ``(none)
        let stx ←
          `(
               ((Sexp.parseTagged sexp $(quote ctorName.eraseMacroScopes.getString!) $(quote ctorInfo.numFields) $(quote userNamesOpt)).bind
                 (fun sexps => do
                   $[let $identNames:ident ← $fromSexps:doExpr]*
                   let res := $(mkIdent ctorName):ident $identNames*
                   return res))
          )
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

private def mkFromSexpBody (ctx : Context) (e : Expr) : TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    mkFromSexpBodyForStruct indName
  else
    mkFromSexpBodyForInduct ctx indName

private def mkFromSexpAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indval     := ctx.typeInfos[i]!
  let header     ←  mkFromSexpHeader indval --TODO fix header info
  let binders    := header.binders
  elabBinders binders fun _ => do
  let type ← elabTerm header.targetType none
  let mut body ← mkFromSexpBody ctx type
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
  trace[Elab.Deriving.toSexp] "\n{cmds}"
  return cmds

private def mkFromSexpInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "fromSexp" declName
  let cmds := #[← mkFromSexpMutualBlock ctx] ++ (← mkInstanceCmds ctx ``FromSexp #[declName])
  trace[Elab.Deriving.fromSexp] "\n{cmds}"
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
