import Lean
import Lean.Data.Format

namespace KLR.Util

open Lean(Format FromJson fromJson? Json ToFormat ToJson toJson)

-- When we need to ability to sort object keys. For example, a bug in NRT means we must have
-- a certain "metadata" field come last in the object list.
inductive ListJson where
| null
| bool (b : Bool)
| num (n : Lean.JsonNumber)
| str (s : String)
| arr (elems : Array ListJson)
| obj (kvPairs : List (String × ListJson))
deriving Inhabited

namespace ListJson

def sortBy (cmp : String -> String -> Bool) : ListJson -> ListJson
| arr elems => arr (elems.map (sortBy cmp))
| obj kvs => obj $ kvs.mergeSort fun (k1, _) (k2, _) => cmp k1 k2
| j => j

partial def toJsonInst : ListJson -> Json
| null => .null
| bool b => .bool b
| num n => .num n
| str s => .str s
| arr a => .arr (a.map toJsonInst)
| obj kvs => Json.mkObj $ kvs.map fun (k, v) => (k, toJsonInst v)

instance : ToJson ListJson where
  toJson := toJsonInst

partial def fromJsonInst : Json -> ListJson
| .null => .null
| .bool b => .bool b
| .num n => .num n
| .str s => .str s
| .arr a => .arr (a.map fromJsonInst)
| .obj kvs => Id.run do
  let mut res := []
  for ⟨ k, v ⟩ in kvs.toArray do
    res := (k, fromJsonInst v) :: res
  return .obj res

instance : FromJson ListJson where
  fromJson? j := return fromJsonInst j

-- borrowed from https://github.com/leanprover/lean4/blob/master/src/Lean/Data/Json/Printer.lean
set_option maxRecDepth 1024 in

/--
This table contains for each UTF-8 byte whether we need to escape a string that contains it.
-/
private def escapeTable : { xs : ByteArray // xs.size = 256 } :=
  ⟨ByteArray.mk #[
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1
  ], by rfl⟩

private def escapeAux (acc : String) (c : Char) : String :=
  -- escape ", \, \n and \r, keep all other characters ≥ 0x20 and render characters < 0x20 with \u
  if c = '"' then -- hack to prevent emacs from regarding the rest of the file as a string: "
    acc ++ "\\\""
  else if c = '\\' then
    acc ++ "\\\\"
  else if c = '\n' then
    acc ++ "\\n"
  else if c = '\x0d' then
    acc ++ "\\r"
  -- the c.val ≤ 0x10ffff check is technically redundant,
  -- since Lean chars are unicode scalar values ≤ 0x10ffff.
  -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
  -- the JSON standard is not definite: both directly printing the character
  -- and encoding it with multiple \u is allowed, and it is up to parsers to make the
  -- decision.
  else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
    acc.push c
  else
    let n := c.toNat;
    -- since c.val < 0x20 in this case, this conversion is more involved than necessary
    -- (but we keep it for completeness)
    let d1 := Nat.digitChar (n / 4096)
    let d2 := Nat.digitChar ((n % 4096) / 256)
    let d3 := Nat.digitChar ((n % 256) / 16)
    let d4 := Nat.digitChar (n % 16)
    acc ++ "\\u" |>.push d1 |>.push d2 |>.push d3 |>.push d4

private def needEscape (s : String) : Bool :=
  go s 0
where
  go (s : String) (i : Nat) : Bool :=
    if h : i < s.utf8ByteSize then
      let byte := s.getUtf8Byte i h
      have h1 : byte.toNat < 256 := UInt8.toNat_lt_size byte
      have h2 : escapeTable.val.size = 256 := escapeTable.property
      if escapeTable.val.get byte.toNat (Nat.lt_of_lt_of_eq h1 h2.symm) == 0 then
        go s (i + 1)
      else
        true
    else
      false

def escape (s : String) (acc : String := "") : String :=
  -- If we don't have any characters that need to be escaped we can just append right away.
  if needEscape s then
    s.foldl escapeAux acc
  else
    acc ++ s

def renderString (s : String) (acc : String := "") : String :=
  let acc := acc ++ "\""
  let acc := escape s acc
  acc ++ "\""

section

partial def render : ListJson → Format
  | null       => "null"
  | bool true  => "true"
  | bool false => "false"
  | num s      => s.toString
  | str s      => renderString s
  | arr elems  =>
    let elems := Format.joinSep (elems.map render).toList ("," ++ Format.line);
    Format.bracket "[" elems "]"
  | obj kvs =>
    let renderKV : String → ListJson → Format := fun k v =>
      Format.group (renderString k ++ ":" ++ Format.line ++ render v);
    let kvs := Format.joinSep (kvs.foldl (init := []) (fun acc (k, j) => renderKV k j :: acc)) ("," ++ Format.line);
    Format.bracket "{" kvs "}"
end

def pretty (j : ListJson) (lineWidth := 80) : String :=
  Format.pretty (render j) lineWidth

inductive CompressWorkItem where
| json (j : ListJson)
| arrayElem (j : ListJson)
| arrayEnd
| objectField (k : String) (j : ListJson)
| objectEnd
| comma

partial def compress (j : ListJson) : String :=
  go "" [.json j]
where go (acc : String) : List CompressWorkItem → String
  | []               => acc
  | .json j :: is =>
    match j with
    | null       => go (acc ++ "null") is
    | bool true  => go (acc ++ "true") is
    | bool false => go (acc ++ "false") is
    | num s      => go (acc ++ s.toString) is
    | str s      => go (renderString s acc) is
    | arr elems  => go (acc ++ "[") ((elems.map .arrayElem).toListAppend (.arrayEnd :: is))
    | obj kvs    => go (acc ++ "{") (kvs.foldl (init := []) (fun acc (k, j) => .objectField k j :: acc) ++ [.objectEnd] ++ is)
  | .arrayElem j :: .arrayEnd :: is      => go acc (.json j :: .arrayEnd :: is)
  | .arrayElem j :: is                  => go acc (.json j :: .comma :: is)
  | .arrayEnd :: is                     => go (acc ++ "]") is
  | .objectField k j :: .objectEnd :: is => go (renderString k acc ++ ":") (.json j :: .objectEnd :: is)
  | .objectField k j :: is              => go (renderString k acc ++ ":") (.json j :: .comma :: is)
  | .objectEnd :: is                    => go (acc ++ "}") is
  | .comma :: is                        => go (acc ++ ",") is

instance : ToFormat ListJson := ⟨render⟩
instance : ToString ListJson := ⟨pretty⟩

#guard
  let f x y := match x, y with
  | "metadata", _ => true
  | _, "metadata" => false
  | x, y => y <= x
  let j := toJson (fromJsonInst (json%{"z":5,"metadata":8, "aa":6,"zz":7}) |> sortBy f)
  j == json%{"aa":6,"z":5,"zz":7,"metadata":8}

end ListJson
end KLR.Util
