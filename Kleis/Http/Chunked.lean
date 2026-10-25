import Kleis.Http.Reader

/-!
# Chunked transfer coding

One reader, `Reader`, which is fed the bytes as they arrive and carries its place
from one read to the next: each byte is looked at once, and it holds no more than
one size or trailer line of the framing.  The data it keeps, up to a limit, or
lets go.  `scan` (where does the body end?) and `decode` (what is its entity?)
are that reader run over a buffer, so every caller agrees on where a body ends —
the line between one message and the next, which a proxy must never draw
differently from the origin.

The framing is read strictly: each line ends in CRLF, and each chunk's data is
followed by exactly CRLF.  A body that is not so framed is refused, not guessed at.
-/

namespace Kleis
namespace Http
namespace Chunked

open LeanBiscuit (Bytes)

/-- The longest a chunk size line may be before we stop waiting for its end. -/
def maxChunkLine : Nat := 8192

/-- The largest number of trailer fields accepted after the last chunk. -/
def maxTrailers : Nat := 64

/-- How far a scan got. -/
inductive Scan where
  /-- The body is incomplete; feed more bytes. -/
  | need
  /-- The body ends after this many bytes of the buffer, trailers included. -/
  | done (consumed : Nat)
  /-- Malformed framing. -/
  | error (message : String)
  deriving Repr, Inhabited

/-- The result of reassembling a body. -/
inductive Decoded where
  /-- Incomplete. -/
  | need
  /-- The entity body, and how many bytes of framing it occupied.  When the
  body was cut short at `limit`, `complete` is false and `consumed` is only the
  framing seen so far. -/
  | done (body : Bytes) (consumed : Nat) (complete : Bool)
  /-- Malformed. -/
  | error (message : String)
  deriving Repr, Inhabited

/-! ## Reading as the bytes arrive -/

/-- Where a reader is in the framing. -/
inductive Phase where
  /-- In a chunk-size line, this much of it seen. -/
  | size (line : Bytes)
  /-- In a chunk's data, this many bytes of it still to come. -/
  | data (left : Nat)
  /-- In the CRLF after a chunk's data, this many of its two bytes still to come. -/
  | gap (left : Nat)
  /-- In the trailer section: the current line so far, and how many more lines it may have. -/
  | trailer (line : Bytes) (left : Nat)
  /-- Past the end. -/
  | finished
  deriving Inhabited

/-- A chunked body being read. -/
structure Reader where
  /-- Where it is. -/
  phase : Phase := .size ByteArray.empty
  /-- The entity bytes kept so far: the data of each chunk, up to `limit`. -/
  entity : Bytes := ByteArray.empty
  /-- How many entity bytes to keep. -/
  limit : Nat := 0
  /-- Whether data past `limit` was let go, so that `entity` is not the whole body. -/
  overflow : Bool := false
  /-- The bytes of the last `feed`, framed again the one way this reader writes chunked
  framing: a chunk per run of data, sized in lowercase hex with no extension, and a bare
  terminator with no trailers.  What kleis sends upstream, so the origin never sees the
  client's framing — however it reads that, it reads this the same way. -/
  emitted : Bytes := ByteArray.empty
  deriving Inhabited

/-- Is the body over? -/
def Reader.finished (r : Reader) : Bool :=
  match r.phase with
  | .finished => true
  | _ => false

/-- A control character: what no line of the framing may carry. -/
private def isControl (c : UInt8) : Bool := c < 32 || c == 127

/-- A hexadecimal digit's value. -/
private def hexDigit? (c : UInt8) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48).toNat
  else if 97 ≤ c && c ≤ 102 then some (c - 87).toNat
  else if 65 ≤ c && c ≤ 70 then some (c - 55).toNat
  else none

/-- A `token` character (RFC 9110 §5.6.2), what a field name is made of. -/
private def isTchar (c : UInt8) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) ||
  "!#$%&'*+-.^_`|~".toUTF8.toList.contains c

/-- Read a chunk-size line, its CR removed: one to sixteen hexadecimal digits and nothing
else — no space around them — then optionally `;` and an extension of no control
characters, which is ignored.  Anything else is not a size line. -/
private def sizeOf? (line : Bytes) : Option Nat := do
  let semi := (Bytes.indexOfByte? line 59).getD line.size
  if semi == 0 || semi > 16 then none
  let mut n := 0
  for k in [0:semi] do
    n := n * 16 + (← hexDigit? (line.get! k))
  if semi < line.size then
    if semi + 1 == line.size then none
    for k in [semi + 1:line.size] do
      if isControl (line.get! k) then none
  pure n

/-- Is this, its CR removed, a trailer field: a name of `token` characters, a colon with
nothing between, and a value of no control characters but tab? -/
private def isTrailerField (line : Bytes) : Bool :=
  match Bytes.indexOfByte? line 58 with
  | none => false
  | some colon =>
    colon > 0 &&
    (List.range colon).all (fun k => isTchar (line.get! k)) &&
    (List.range (line.size - colon - 1)).all fun k =>
      let c := line.get! (colon + 1 + k)
      c == 9 || !isControl c

/-- Feed the reader the next bytes. On the end of the body, also the number of
these bytes that belonged to it: the rest are whatever the client sent next. -/
def Reader.feed (r : Reader) (buf : Bytes) : Except String (Reader × Option Nat) := do
  let mut r := { r with emitted := ByteArray.empty }
  let mut i := 0
  -- Each pass consumes at least one byte, or ends.
  for _ in [0:buf.size + 1] do
    if i ≥ buf.size then break
    match r.phase with
    | .finished => break
    | .data left =>
      let n := min left (buf.size - i)
      let keep := min n (r.limit - min r.limit r.entity.size)
      if keep > 0 then r := { r with entity := r.entity ++ Bytes.slice buf i (i + keep) }
      if keep < n then r := { r with overflow := true }
      if n > 0 then
        r := { r with emitted := r.emitted ++ Bytes.ofString s!"{Str.toHex n}\r\n" ++
                                 Bytes.slice buf i (i + n) ++ Bytes.ofString "\r\n" }
      i := i + n
      r := { r with phase := if left == n then .gap 2 else .data (left - n) }
    | .gap left =>
      -- Exactly CRLF: anything else there is not this framing, and a reader that
      -- skipped it would disagree with an origin that does not.
      let want : UInt8 := if left == 2 then 13 else 10
      if buf.get! i != want then throw "a chunk's data must be followed by CRLF"
      i := i + 1
      r := { r with phase := if left == 1 then .size ByteArray.empty else .gap (left - 1) }
    | .size line =>
      match Bytes.indexOfByte? buf 10 i with
      | none =>
        let line := line ++ Bytes.drop buf i
        if line.size > maxChunkLine then throw "chunk size line too long"
        r := { r with phase := .size line }
        i := buf.size
      | some nl =>
        let line := line ++ Bytes.slice buf i nl
        if line.size > maxChunkLine then throw "chunk size line too long"
        if line.size == 0 || line.get! (line.size - 1) != 13 then
          throw "a chunk size line must end in CRLF"
        i := nl + 1
        match sizeOf? (Bytes.take line (line.size - 1)) with
        | none => throw "malformed chunk size line"
        | some 0 => r := { r with phase := .trailer ByteArray.empty maxTrailers }
        | some n => r := { r with phase := .data n }
    | .trailer line left =>
      match Bytes.indexOfByte? buf 10 i with
      | none =>
        let line := line ++ Bytes.drop buf i
        if line.size > maxChunkLine then throw "trailer line too long"
        r := { r with phase := .trailer line left }
        i := buf.size
      | some nl =>
        let line := line ++ Bytes.slice buf i nl
        if line.size > maxChunkLine then throw "trailer line too long"
        if line.size == 0 || line.get! (line.size - 1) != 13 then
          throw "a trailer line must end in CRLF"
        i := nl + 1
        let field := Bytes.take line (line.size - 1)
        -- The section ends at an empty line and nothing else: a line of spaces is
        -- neither an end nor a field, and an origin might take it for either.
        if field.size == 0 then
          return ({ r with phase := .finished, emitted := r.emitted ++ Bytes.ofString "0\r\n\r\n" },
                  some i)
        if !isTrailerField field then throw "malformed trailer field"
        -- Read and checked, then dropped: nothing decides on a trailer, so none is sent on.
        match left with
        | 0 => throw "too many trailer fields"
        | left + 1 => r := { r with phase := .trailer ByteArray.empty left }
  return (r, if r.finished then some i else none)

/-- Find the end of a chunked body.  The same reader as everywhere else, so that what
ends a body for the relay ends it for every other caller too. -/
def scan (buf : Bytes) : Scan :=
  match ({} : Reader).feed buf with
  | .ok (_, some consumed) => .done consumed
  | .ok (_, none) => .need
  | .error e => .error e

/-- Reassemble a chunked body, up to `limit` entity bytes: complete if the body ended
within the limit, cut short (and not complete) once the limit is reached. -/
def decode (buf : Bytes) (limit : Nat) : Decoded :=
  match ({ limit } : Reader).feed buf with
  | .ok (r, some consumed) => .done r.entity consumed (!r.overflow)
  | .ok (r, none) => if r.entity.size ≥ limit then .done r.entity buf.size false else .need
  | .error e => .error e

/-- Frame a payload as a single chunk followed by the terminator. -/
def encodeAll (body : Bytes) : Bytes :=
  if body.size == 0 then Bytes.ofString "0\r\n\r\n"
  else Bytes.ofString s!"{Str.toHex body.size}\r\n" ++ body ++ Bytes.ofString "\r\n0\r\n\r\n"

end Chunked
end Http
end Kleis
