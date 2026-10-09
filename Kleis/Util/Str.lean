import LeanBiscuit

/-!
# Text helpers

Header names, path segments and query parameters all need the same handful of
operations, and all of them have to agree with what the client did or the match
will silently fail.  The rules that matter: header names are compared
case-insensitively (RFC 9110), percent decoding happens once and never twice,
and a path is split on `/` with the leading empty segment dropped.
-/

namespace Kleis
namespace Str

/-- ASCII lowercase.  Deliberately not `String.toLower`, which is locale-free
but still maps non-ASCII; a header name is ASCII by definition and a byte that
is not must not be folded into one that is. -/
def toLowerAscii (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)

/-- Drop ASCII spaces and tabs from both ends. -/
def trim (s : String) : String := s.trimAscii.toString

/-- Split on the first occurrence of `sep`. -/
def splitOnce? (s : String) (sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | [] => none
  | [_] => none
  | a :: rest => some (a, sep.intercalate rest)

/-- The value of a hexadecimal digit. -/
private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Percent-decode, optionally treating `+` as a space (which is correct for a
query string and wrong for a path).

Invalid escapes are left alone rather than rejected: a path the origin server
would have accepted must not become a proxy error, and the facts we derive from
it are compared against manifest patterns that see the same bytes. -/
def percentDecode (s : String) (plusIsSpace : Bool := false) : String :=
  -- As bytes first, so that an escaped UTF-8 sequence becomes the one character it
  -- encodes rather than one character per byte; percentEncode turns it back into the
  -- same escapes.  Bytes that are not UTF-8 fall back to one character per byte.
  let rec bytes (cs : List Char) (acc : Array UInt8) : Array UInt8 :=
    match cs with
    | [] => acc
    | '%' :: a :: b :: rest =>
      match hexVal? a, hexVal? b with
      | some x, some y => bytes rest (acc.push (UInt8.ofNat (x * 16 + y)))
      | _, _ => bytes (a :: b :: rest) (acc.push 37)
    | '+' :: rest => bytes rest (acc.push (if plusIsSpace then 32 else 43))
    | c :: rest => bytes rest (acc ++ (String.singleton c).toUTF8.data)
  match String.fromUTF8? (ByteArray.mk (bytes s.toList #[])) with
  | some decoded => decoded
  | none =>
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '%' :: a :: b :: rest =>
      match hexVal? a, hexVal? b with
      | some x, some y => go rest (Char.ofNat (x * 16 + y) :: acc)
      | _, _ => go (a :: b :: rest) ('%' :: acc)
    | '+' :: rest => go rest ((if plusIsSpace then ' ' else '+') :: acc)
    | c :: rest => go rest (c :: acc)
  String.ofList (go s.toList [])

/-- Percent-encode everything outside the unreserved set. -/
def percentEncode (s : String) : String :=
  let unreserved (c : Char) :=
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') ||
      c == '-' || c == '.' || c == '_' || c == '~'
  let hex (n : Nat) := "0123456789ABCDEF".toList[n]!
  String.ofList (s.toUTF8.toList.flatMap fun b =>
    let c := Char.ofNat b.toNat
    if b < 128 && unreserved c then [c]
    else ['%', hex (b.toNat / 16), hex (b.toNat % 16)])

/-- Split a path into its segments, dropping the empty ones that a leading or
doubled `/` produces, and percent-decoding each. -/
def pathSegments (path : String) : Array String :=
  let raw := (path.splitOn "?").headD path
  (raw.splitOn "/").foldl (init := #[]) fun acc seg =>
    if seg.isEmpty then acc else acc.push (percentDecode seg)

/-- The path with any query string removed. -/
def pathOnly (target : String) : String := (target.splitOn "?").headD target

/-- Parse a query string into decoded name/value pairs.  A parameter with no
`=` gets the empty string, matching what every server does with it. -/
def parseQuery (target : String) : Array (String × String) :=
  match splitOnce? target "?" with
  | none => #[]
  | some (_, q) =>
    (q.splitOn "&").foldl (init := #[]) fun acc part =>
      if part.isEmpty then acc
      else match splitOnce? part "=" with
        | some (k, v) => acc.push (percentDecode k true, percentDecode v true)
        | none => acc.push (percentDecode part true, "")

/-- Strip a suffix if present. -/
def stripSuffix (s suffix : String) : String :=
  if suffix.isEmpty || !s.endsWith suffix then s
  else (s.take (s.length - suffix.length)).toString

/-- Strip a prefix if present. -/
def stripPrefix (s pre : String) : String :=
  if pre.isEmpty || !s.startsWith pre then s else (s.drop pre.length).toString

/-- Is every character an ASCII digit, with at least one? -/
def isDigits (s : String) : Bool := !s.isEmpty && s.toList.all fun c => '0' ≤ c && c ≤ '9'

/-- Render a `Nat` in lowercase hexadecimal, without a leading `0x`. -/
def toHex (n : Nat) : String :=
  if n == 0 then "0" else
    let rec go (n : Nat) (acc : List Char) : List Char :=
      if h : n = 0 then acc
      else go (n / 16) ("0123456789abcdef".toList[n % 16]! :: acc)
    termination_by n
    decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)
    String.ofList (go n [])

/-- Read a lowercase or uppercase hexadecimal literal. -/
def ofHex? (s : String) : Option Nat := do
  if s.isEmpty then none else
    s.toList.foldlM (init := 0) fun acc c => do
      let d ← hexVal? c
      pure (acc * 16 + d)

end Str
end Kleis
