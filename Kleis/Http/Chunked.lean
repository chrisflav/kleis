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
  deriving Inhabited

/-- Is the body over? -/
def Reader.finished (r : Reader) : Bool :=
  match r.phase with
  | .finished => true
  | _ => false

/-- Read a chunk-size line: the size, with any extension after `;` ignored. -/
private def sizeOf? (line : Bytes) : Option Nat :=
  let text := Bytes.toStringLossy line
  Str.ofHex? (Str.trim ((text.splitOn ";").headD text))

/-- Feed the reader the next bytes. On the end of the body, also the number of
these bytes that belonged to it: the rest are whatever the client sent next. -/
def Reader.feed (r : Reader) (buf : Bytes) : Except String (Reader × Option Nat) := do
  let mut r := r
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
        match sizeOf? line with
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
        if (Bytes.trim line).size == 0 then
          return ({ r with phase := .finished }, some i)
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
