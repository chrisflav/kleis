import Kleis.Util.Str
import LeanBiscuit

/-!
# JSON

A total JSON reader and writer, used for three unrelated things: request bodies
the policy layer reasons about, the daemon's control API, and the audit log.

Written here rather than taken from `Lean.Data.Json` for the same reason
`lean-biscuit` writes its own protobuf: everything the policy layer touches has
to be pure and total, and the recursion has to be bounded by something the
input determines.  Here that bound is the length of the source — a value cannot
nest more deeply than there are characters to open it with.

Numbers keep their source text.  Biscuit datalog has integers and no floats, so
a number that is not an integer would have to be rounded or rejected; keeping
the text lets `toValue` map it to a string instead and lose nothing.
-/

namespace Kleis

/-- A JSON value. -/
inductive Json where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (value : Bool)
  /-- A number, as it was written. -/
  | num (raw : String)
  /-- A string, unescaped. -/
  | str (value : String)
  /-- An array. -/
  | arr (elements : List Json)
  /-- An object, in source order. -/
  | obj (fields : List (String × Json))
  deriving Repr, Inhabited

namespace Json

/-! ## Reading -/

/-- The parser state: the source and how far into it we are. -/
private structure P where
  /-- The source, as characters. -/
  src : Array Char
  /-- The current offset. -/
  pos : Nat

private def peek? (p : P) : Option Char :=
  if h : p.pos < p.src.size then some p.src[p.pos] else none

private def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def skipWs (p : P) : P :=
  let rec go (p : P) (fuel : Nat) : P :=
    match fuel with
    | 0 => p
    | fuel + 1 => match peek? p with
      | some c => if isWs c then go { p with pos := p.pos + 1 } fuel else p
      | none => p
  go p p.src.size

private def expect (p : P) (c : Char) : Except String P :=
  match peek? p with
  | some c' => if c' == c then .ok { p with pos := p.pos + 1 }
               else throw s!"expected `{c}` at offset {p.pos}"
  | none => throw s!"expected `{c}` but the input ended"

private def literal (p : P) (s : String) : Except String P :=
  let cs := s.toList
  let ok := cs.zipIdx.all fun (c, i) =>
    match (if h : p.pos + i < p.src.size then some p.src[p.pos + i] else none) with
    | some c' => c' == c
    | none => false
  if ok then .ok { p with pos := p.pos + cs.length }
  else throw s!"expected `{s}` at offset {p.pos}"

/-- Read four hexadecimal digits as a code unit. -/
private def hex4 (p : P) : Except String (Nat × P) := do
  let digits := (List.range 4).map fun i =>
    if h : p.pos + i < p.src.size then some p.src[p.pos + i] else none
  match digits.mapM id with
  | none => throw "truncated \\u escape"
  | some cs =>
    match Str.ofHex? (String.ofList cs) with
    | none => throw s!"malformed \\u escape at offset {p.pos}"
    | some n => pure (n, { p with pos := p.pos + 4 })

/-- Read a string body, the opening quote already consumed. -/
private def stringBody (p : P) : Except String (String × P) :=
  let rec go (p : P) (acc : List Char) (fuel : Nat) : Except String (String × P) :=
    match fuel with
    | 0 => throw "unterminated string"
    | fuel + 1 =>
      match peek? p with
      | none => throw "unterminated string"
      | some '"' => .ok (String.ofList acc.reverse, { p with pos := p.pos + 1 })
      | some '\\' =>
        let p := { p with pos := p.pos + 1 }
        match peek? p with
        | none => throw "unterminated escape"
        | some c =>
          let p1 := { p with pos := p.pos + 1 }
          match c with
          | '"' => go p1 ('"' :: acc) fuel
          | '\\' => go p1 ('\\' :: acc) fuel
          | '/' => go p1 ('/' :: acc) fuel
          | 'b' => go p1 (Char.ofNat 8 :: acc) fuel
          | 'f' => go p1 (Char.ofNat 12 :: acc) fuel
          | 'n' => go p1 ('\n' :: acc) fuel
          | 'r' => go p1 ('\r' :: acc) fuel
          | 't' => go p1 ('\t' :: acc) fuel
          | 'u' => do
            let (hi, p2) ← hex4 p1
            -- A high surrogate is only meaningful paired with a low one; an
            -- unpaired one is replaced rather than rejected, so that a body a
            -- server would accept does not become a proxy error.
            if 0xD800 ≤ hi && hi ≤ 0xDBFF then
              match literal p2 "\\u" with
              | .error _ => go p2 (Char.ofNat 0xFFFD :: acc) fuel
              | .ok p3 => do
                let (lo, p4) ← hex4 p3
                if 0xDC00 ≤ lo && lo ≤ 0xDFFF then
                  let cp := 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)
                  go p4 (Char.ofNat cp :: acc) fuel
                else go p4 (Char.ofNat 0xFFFD :: Char.ofNat 0xFFFD :: acc) fuel
            else if 0xDC00 ≤ hi && hi ≤ 0xDFFF then go p2 (Char.ofNat 0xFFFD :: acc) fuel
            else go p2 (Char.ofNat hi :: acc) fuel
          | c => throw s!"unknown escape `\\{c}`"
      | some c =>
        if c.toNat < 0x20 then throw "a control character in a string must be escaped"
        else go { p with pos := p.pos + 1 } (c :: acc) fuel
  go p [] (p.src.size + 1)

/-- Read a number, keeping its source text. -/
private def number (p : P) : Except String (String × P) :=
  let isNum (c : Char) :=
    ('0' ≤ c && c ≤ '9') || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel + 1 =>
      if h : i < p.src.size then (if isNum p.src[i] then go (i + 1) fuel else i) else i
  let stop := go p.pos p.src.size
  if stop == p.pos then throw s!"expected a value at offset {p.pos}"
  else .ok (String.ofList ((p.src.extract p.pos stop).toList), { p with pos := stop })

mutual

/-- Read any value. -/
private def value (p : P) (fuel : Nat) : Except String (Json × P) := do
  match fuel with
  | 0 => throw "JSON nested too deeply"
  | fuel + 1 =>
    let p := skipWs p
    match peek? p with
    | none => throw "the input ended where a value was expected"
    | some '{' => object { p with pos := p.pos + 1 } fuel
    | some '[' => array { p with pos := p.pos + 1 } fuel
    | some '"' => do
      let (s, p) ← stringBody { p with pos := p.pos + 1 }
      pure (.str s, p)
    | some 't' => do pure (.bool true, ← literal p "true")
    | some 'f' => do pure (.bool false, ← literal p "false")
    | some 'n' => do pure (.null, ← literal p "null")
    | some _ => do
      let (n, p) ← number p
      pure (.num n, p)

/-- Read the rest of an array, the `[` already consumed. -/
private def array (p : P) (fuel : Nat) : Except String (Json × P) := do
  let p := skipWs p
  match peek? p with
  | some ']' => pure (.arr [], { p with pos := p.pos + 1 })
  | _ => do
    let (elems, p) ← arrayItems p fuel []
    pure (.arr elems, p)

/-- Read array elements separated by commas. -/
private def arrayItems (p : P) (fuel : Nat) (acc : List Json) :
    Except String (List Json × P) := do
  match fuel with
  | 0 => throw "JSON nested too deeply"
  | fuel + 1 =>
    let (v, p) ← value p fuel
    let p := skipWs p
    match peek? p with
    | some ',' => arrayItems { p with pos := p.pos + 1 } fuel (v :: acc)
    | some ']' => pure ((v :: acc).reverse, { p with pos := p.pos + 1 })
    | _ => throw s!"expected `,` or `]` at offset {p.pos}"

/-- Read the rest of an object, the `{` already consumed. -/
private def object (p : P) (fuel : Nat) : Except String (Json × P) := do
  let p := skipWs p
  match peek? p with
  | some '}' => pure (.obj [], { p with pos := p.pos + 1 })
  | _ => do
    let (fields, p) ← objectFields p fuel []
    pure (.obj fields, p)

/-- Read object members separated by commas. -/
private def objectFields (p : P) (fuel : Nat) (acc : List (String × Json)) :
    Except String (List (String × Json) × P) := do
  match fuel with
  | 0 => throw "JSON nested too deeply"
  | fuel + 1 =>
    let p := skipWs p
    let p ← expect p '"'
    let (k, p) ← stringBody p
    let p := skipWs p
    let p ← expect p ':'
    let (v, p) ← value p fuel
    let p := skipWs p
    match peek? p with
    | some ',' => objectFields { p with pos := p.pos + 1 } fuel ((k, v) :: acc)
    | some '}' => pure (((k, v) :: acc).reverse, { p with pos := p.pos + 1 })
    | _ => throw s!"expected `,` or `}}` at offset {p.pos}"

end

/-- Parse a complete JSON document. -/
def parse (s : String) : Except String Json := do
  let src := s.toList.toArray
  let (v, p) ← value ⟨src, 0⟩ (src.size + 1)
  let p := skipWs p
  if p.pos < p.src.size then throw s!"trailing input at offset {p.pos}" else pure v

/-! ## Writing -/

/-- Escape a string for output. -/
def escape (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c == '"' then ['\\', '"']
    else if c == '\\' then ['\\', '\\']
    else if c == '\n' then ['\\', 'n']
    else if c == '\r' then ['\\', 'r']
    else if c == '\t' then ['\\', 't']
    else if c.toNat < 0x20 then
      let h := Str.toHex c.toNat
      let pad := String.ofList (List.replicate (4 - h.length) '0')
      ('\\' :: 'u' :: (pad ++ h).toList)
    else [c])

mutual

/-- Render, compactly. -/
def render : Json → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num n => n
  | .str s => "\"" ++ escape s ++ "\""
  | .arr l => "[" ++ renderList l ++ "]"
  | .obj fs => "{" ++ renderFields fs ++ "}"

/-- Render array elements, comma separated. -/
def renderList : List Json → String
  | [] => ""
  | [x] => render x
  | x :: xs => render x ++ ", " ++ renderList xs

/-- Render object members, comma separated. -/
def renderFields : List (String × Json) → String
  | [] => ""
  | [(k, v)] => "\"" ++ escape k ++ "\": " ++ render v
  | (k, v) :: xs => "\"" ++ escape k ++ "\": " ++ render v ++ ", " ++ renderFields xs

end

/-! ## Access -/

/-- The value of an object field. -/
def field? : Json → String → Option Json
  | .obj fs, k => (fs.find? fun (k', _) => k' == k).map (·.2)
  | _, _ => none

/-- As a string. -/
def asString? : Json → Option String
  | .str s => some s
  | _ => none

/-- As an integer. -/
def asInt? : Json → Option Int
  | .num n => n.toInt?
  | _ => none

/-- As a boolean. -/
def asBool? : Json → Option Bool
  | .bool b => some b
  | _ => none

/-- As a list of elements. -/
def asArray? : Json → Option (List Json)
  | .arr l => some l
  | _ => none

/-- A string field. -/
def str? (j : Json) (k : String) : Option String := j.field? k >>= asString?

/-- An integer field. -/
def int? (j : Json) (k : String) : Option Int := j.field? k >>= asInt?

/-- A boolean field. -/
def bool? (j : Json) (k : String) : Option Bool := j.field? k >>= asBool?

/-- An array field, defaulting to empty. -/
def arr? (j : Json) (k : String) : List Json := (j.field? k >>= asArray?).getD []

/-! ## To datalog -/

open LeanBiscuit.Datalog

/-! A number that is not an integer becomes its source text as a string:
biscuit datalog has no floating point type, and rounding a price or a version
into an integer would be a silent lie in a policy decision.  A rule that wants
to compare such a field has the text and can say so. -/

mutual

/-- Translate into a datalog value. -/
def toValue : Json → Value
  | .null => .null
  | .bool b => .bool b
  | .num n => match n.toInt? with
    | some i => .integer i
    | none => .str n
  | .str s => .str s
  | .arr l => .array (toValueList l)
  | .obj fs => .map (toValueFields fs)

/-- Translate each element of an array. -/
def toValueList : List Json → List Value
  | [] => []
  | x :: xs => toValue x :: toValueList xs

/-- Translate each member of an object. -/
def toValueFields : List (String × Json) → List (ValueKey × Value)
  | [] => []
  | (k, v) :: xs => (ValueKey.str k, toValue v) :: toValueFields xs

end

end Json
end Kleis
