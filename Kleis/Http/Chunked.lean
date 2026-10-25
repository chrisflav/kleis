import Kleis.Http.Reader

/-!
# Chunked transfer coding

Two jobs, and they are deliberately separate.

`decode` reassembles a body from a buffer, for the case where the body has to
be *understood*: a decoder wants a prefix of the entity, not a prefix of its
framing.

`scan` finds where a body ends without reassembling it, for the case where the
body is merely being relayed.  A push of a hundred megabytes goes through
`scan`, and the proxy never holds more than one chunk header.

Neither is `partial`.  Every chunk costs at least three bytes of framing — a
size digit and a CRLF — so a buffer of `n` bytes holds fewer than `n` chunks,
and that is the fuel both loops are given.
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

/-- Parse a chunk size line at `i`, returning the size and the index just past
its line feed.  A chunk extension after `;` is ignored, as it must be. -/
private def chunkHeader? (buf : Bytes) (i : Nat) : Option (Nat × Nat) := do
  let nl ← Bytes.indexOfByte? buf 10 i
  let line := Bytes.toStringLossy (Bytes.slice buf i nl)
  let line := (line.splitOn ";").headD line
  let size ← Str.ofHex? (Str.trim line)
  pure (size, nl + 1)

/-- Skip the trailer section, which ends at the first empty line. -/
private def trailers (buf : Bytes) : Nat → Nat → Scan
  | _, 0 => .error "too many trailer fields"
  | i, fuel + 1 =>
    match Bytes.indexOfByte? buf 10 i with
    | none => if buf.size - i > maxChunkLine then .error "trailer line too long" else .need
    | some nl =>
      if (Bytes.trim (Bytes.slice buf i nl)).size == 0 then .done (nl + 1)
      else trailers buf (nl + 1) fuel

/-- Find the end of a chunked body, without copying it. -/
private def scanFrom (buf : Bytes) : Nat → Nat → Scan
  | _, 0 => .error "chunked body has too many chunks"
  | i, fuel + 1 =>
    match chunkHeader? buf i with
    | none =>
      if buf.size - i > maxChunkLine then .error "chunk size line too long" else .need
    | some (0, afterHeader) => trailers buf afterHeader maxTrailers
    | some (size, afterHeader) =>
      let next := afterHeader + size + 2
      if next > buf.size then .need else scanFrom buf next fuel

/-- Find the end of a chunked body. -/
def scan (buf : Bytes) : Scan := scanFrom buf 0 (buf.size + 1)

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

/-- Reassemble a chunked body, stopping once `limit` entity bytes are in hand.

Stopping early is the point: a decoder is given a prefix and either decides or
asks for more, so the proxy never has to hold a whole push in memory to find
out which refs it updates. -/
private def decodeFrom (buf : Bytes) (limit : Nat) : Nat → Bytes → Nat → Decoded
  | _, _acc, 0 => .error "chunked body has too many chunks"
  | i, acc, fuel + 1 =>
    if acc.size ≥ limit then .done acc i false
    else match chunkHeader? buf i with
      | none =>
        if buf.size - i > maxChunkLine then .error "chunk size line too long" else .need
      | some (0, afterHeader) =>
        match trailers buf afterHeader maxTrailers with
        | .done consumed => .done acc consumed true
        | .need => .need
        | .error e => .error e
      | some (size, afterHeader) =>
        let next := afterHeader + size + 2
        if next > buf.size then .need
        else decodeFrom buf limit next (acc ++ Bytes.slice buf afterHeader (afterHeader + size)) fuel

/-- Reassemble a chunked body, up to `limit` entity bytes. -/
def decode (buf : Bytes) (limit : Nat) : Decoded :=
  decodeFrom buf limit 0 ByteArray.empty (buf.size + 1)

/-! ## Reading as the bytes arrive

`scan` and `decode` start from the beginning of their buffer, which is right for
a buffer that is whole and wrong for one that grows a read at a time: asked
again after every read, they cost the square of the body.  A `Reader` carries
where it is from one read to the next instead, so each byte is looked at once,
and it holds no more than one header or trailer line of the framing — the data
it either keeps, up to a limit, or lets go. -/

/-- Where a reader is in the framing. -/
inductive Phase where
  /-- In a chunk-size line, this much of it seen. -/
  | size (line : Bytes)
  /-- In a chunk's data, this many bytes of it still to come. -/
  | data (left : Nat)
  /-- In the two bytes after a chunk's data, this many still to come. -/
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
      let n := min left (buf.size - i)
      i := i + n
      r := { r with phase := if left == n then .size ByteArray.empty else .gap (left - n) }
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
        i := nl + 1
        if (Bytes.trim line).size == 0 then
          return ({ r with phase := .finished }, some i)
        match left with
        | 0 => throw "too many trailer fields"
        | left + 1 => r := { r with phase := .trailer ByteArray.empty left }
  return (r, if r.finished then some i else none)

/-- Frame a payload as a single chunk followed by the terminator. -/
def encodeAll (body : Bytes) : Bytes :=
  if body.size == 0 then Bytes.ofString "0\r\n\r\n"
  else Bytes.ofString s!"{Str.toHex body.size}\r\n" ++ body ++ Bytes.ofString "\r\n0\r\n\r\n"

end Chunked
end Http
end Kleis
