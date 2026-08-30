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

/-- Frame a payload as a single chunk followed by the terminator. -/
def encodeAll (body : Bytes) : Bytes :=
  if body.size == 0 then Bytes.ofString "0\r\n\r\n"
  else Bytes.ofString s!"{Str.toHex body.size}\r\n" ++ body ++ Bytes.ofString "\r\n0\r\n\r\n"

end Chunked
end Http
end Kleis
