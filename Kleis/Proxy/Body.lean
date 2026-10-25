import Kleis.Http.Chunked
import Kleis.Wire.Exec
import Kleis.Net.Stream

/-!
# Reading enough of a body, and no more

The proxy reads a *prefix* of the body — whatever the decoder asked for, capped
— decides on it, and then relays the rest without holding it.

Two representations are kept and they are not the same thing.  `raw` is the
bytes as they arrived, framing included, and is what gets forwarded: replaying
it verbatim means the origin sees the chunking the client chose, and the proxy
never has to re-frame anything.  `entity` is the decoded body, chunk headers
removed, and is what the decoder and the policy see.

Conflating the two is how a proxy ends up either corrupting a chunked upload or
letting policy read chunk headers as content.
-/

namespace Kleis
namespace Proxy

open LeanBiscuit (Bytes)

/-- What was read of a body. -/
structure BodyPrefix where
  /-- The bytes as they arrived, framing included, and nothing past its end. -/
  raw : Bytes
  /-- The entity bytes, framing removed. -/
  entity : Bytes
  /-- Whether `entity` is the whole body. -/
  complete : Bool
  /-- Whether the framing has been consumed to its end, so that nothing more
  need be relayed. -/
  framingDone : Bool
  /-- Bytes that arrived after the body ended: the start of a request the client
  pipelined behind this one.  Never part of `raw`, and so never relayed with it. -/
  excess : Bytes := ByteArray.empty
  /-- For a chunked request body, the reader where the prefix left it: `raw` is then
  the body framed again by kleis, and the relay goes on framing the rest the same way.
  `none` for a body relayed as it arrived (a response's). -/
  chunked : Option Http.Chunked.Reader := none
  deriving Inhabited

/-- Nothing at all. -/
def BodyPrefix.empty : BodyPrefix :=
  { raw := ByteArray.empty, entity := ByteArray.empty, complete := true, framingDone := true }

/-- Split bytes at the end of a message body under its framing: what belongs to
the body, and what came after it.

This is the line between one message and the next on a connection, and getting
it wrong is request smuggling: bytes past the end of a body, relayed as if they
were part of it, reach the origin as a second request nobody authorized, and
leave a response on the connection for whoever uses it next. -/
def splitAtFraming (framing : Http.Framing) (raw : Bytes) : Bytes × Bytes :=
  match framing with
  | .empty => (ByteArray.empty, raw)
  | .length n => (Bytes.take raw n, Bytes.drop raw n)
  | .chunked =>
    match Http.Chunked.scan raw with
    | .done consumed => (Bytes.take raw consumed, Bytes.drop raw consumed)
    | _ => (raw, ByteArray.empty)
  | .untilClose => (raw, ByteArray.empty)

/-- What has been read of a body so far, kept so that each read costs what it
brought and no more: the bytes are appended once, the chunked framing is read
once, and nothing is rescanned from the start. -/
private structure Progress where
  /-- The body's bytes as they are to be sent on, never past its end: as they arrived,
  or for chunked framing, framed again. -/
  raw : Bytes := ByteArray.empty
  /-- What arrived after the end. -/
  excess : Bytes := ByteArray.empty
  /-- The chunked framing, read so far. -/
  chunked : Http.Chunked.Reader := {}
  /-- Whether the framing has ended. -/
  ended : Bool := false

/-- Take in the next bytes the client sent. -/
private def Progress.feed (p : Progress) (framing : Http.Framing) (chunk : Bytes) :
    Except String Progress := do
  if p.ended then return { p with excess := p.excess ++ chunk }
  match framing with
  | .empty => return { p with ended := true, excess := p.excess ++ chunk }
  | .length n =>
    let k := min chunk.size (n - min n p.raw.size)
    let raw := p.raw ++ Bytes.take chunk k
    return { p with raw, excess := Bytes.drop chunk k, ended := raw.size ≥ n }
  | .chunked =>
    match p.chunked.feed chunk with
    | .error e => throw e
    -- What goes upstream is the body framed again, not the client's framing.
    | .ok (r, some k) =>
      return { p with raw := p.raw ++ r.emitted, excess := Bytes.drop chunk k
                      chunked := r, ended := true }
    | .ok (r, none) => return { p with raw := p.raw ++ r.emitted, chunked := r }
  | .untilClose => return { p with raw := p.raw ++ chunk }

/-- The entity bytes in hand, and whether they are the whole body. -/
private def Progress.entity (p : Progress) (framing : Http.Framing) : Bytes × Bool :=
  match framing with
  | .empty => (ByteArray.empty, true)
  | .length _ => (p.raw, p.ended)
  -- Data let go past the limit means the entity is not the body, ended or not.
  | .chunked => (p.chunked.entity, p.ended && !p.chunked.overflow)
  | .untilClose => (p.raw, false)

/-- The chunked reader to hand on to the relay, for a chunked body. -/
private def chunkedState (framing : Http.Framing) (p : Progress) : Option Http.Chunked.Reader :=
  if framing == .chunked then some p.chunked else none

/-- The most reads one body prefix may take.  A client writing a large body in pieces
of under about 128 bytes (2 MiB over 16384 reads) runs out of them, and its body is
relayed undecoded, which a grant reading it refuses. -/
def maxPrefixReads : Nat := 16384

/-- Read from the client until the decoder is satisfied, the framing ends, or
the cap is reached.

`already` is whatever was read past the head while looking for it — a client
that pipelines the body into the same packet as the request line, which every
git client does.  Anything past the end of the body is returned as `excess`,
never as part of the body.

The decoder is asked again only once at least what it asked for has arrived, and
then at least twice what it was last shown, so however small the client's reads
and however little a decoder asks for at a time, it reads the prefix a bounded
number of times over: the total is linear in the prefix. -/
def readBodyPrefix (s : Net.Stream) (framing : Http.Framing) (decoder : Wire.Decoder)
    (already : Bytes) (cap : Nat) :
    IO (BodyPrefix × Option LeanBiscuit.Datalog.Value) := do
  if framing == .empty then return ({ BodyPrefix.empty with excess := already }, none)
  let malformed (e : String) := IO.userError s!"malformed request body: {e}"
  let mut p : Progress := { chunked := { limit := cap } }
  p ← match p.feed framing already with
    | .ok q => pure q
    | .error e => throw (malformed e)
  -- How many entity bytes to have before asking the decoder again.
  let mut target := 0
  for _ in [0:maxPrefixReads] do
    let (entity, complete) := p.entity framing
    let seen : BodyPrefix := { raw := p.raw, entity, complete, framingDone := p.ended
                               excess := p.excess, chunked := chunkedState framing p }
    let atCap := entity.size ≥ cap || p.raw.size ≥ cap * 2
    if complete || atCap || entity.size ≥ target then
      -- An out-of-process decoder is only worth starting once, so it waits for
      -- the whole prefix.
      let verdict : Wire.Decoded := match decoder with
        | .pure d => d.step entity complete
        | .exec _ _ => if complete || atCap then .opaque else .need (entity.size + 1)
        | .opaque => .opaque
      match verdict with
      | .done value _ => return (seen, some value)
      | .opaque =>
        match decoder with
        -- Only a whole body: a decoder run on a prefix cut off at the cap would answer
        -- for bytes it never saw, and nothing would mark the answer as partial.
        | .exec command args =>
          if complete then return (seen, ← Wire.runExec command args entity)
          else return (seen, none)
        | _ => return (seen, none)
      | .need atLeast =>
        -- Past the cap the body is relayed but not understood, and the authorizer's
        -- truncation guard turns that into a refusal for any policy that depended on it.
        if complete || atCap then return (seen, none)
        target := min cap (max atLeast (2 * entity.size))
    let chunk ← s.read (min 65536 (max 4096 (target - min target entity.size)))
    -- A client that goes away mid-body has sent a truncated request, which is not one
    -- to decide on or forward as if it were whole.
    if chunk.size == 0 then throw (IO.userError "the client closed mid-body")
    p ← match p.feed framing chunk with
      | .ok q => pure q
      | .error e => throw (malformed e)
  let (entity, complete) := p.entity framing
  return ({ raw := p.raw, entity, complete, framingDone := p.ended, excess := p.excess,
             chunked := chunkedState framing p }, none)

/-- Relay the rest of a body from one side to the other, returning whatever was
read past its end.

Nothing is buffered: a chunk is read and written, and the loop ends when the
framing says the body is over.  A read can carry bytes from beyond that point —
the next message on the connection — and those are cut off and returned rather
than relayed, since relaying them is exactly how a second, unauthorized request
gets onto a connection to the origin. -/
def relayBody (from_ to : Net.Stream) (framing : Http.Framing) (sent : BodyPrefix) :
    IO Bytes := do
  if sent.framingDone then return ByteArray.empty
  match framing with
  | .empty => return ByteArray.empty
  | .length n => do
    -- Reads are bounded by what remains, so nothing past the end is ever read.
    let rec goLength (remaining : Nat) (fuel : Nat) : IO Bytes := do
      if remaining == 0 then return ByteArray.empty
      match fuel with
      | 0 => throw (IO.userError "the body did not end")
      | fuel + 1 => do
        let chunk ← from_.read (min remaining 65536)
        if chunk.size == 0 then throw (IO.userError "the connection closed mid-body")
        to.write chunk
        goLength (remaining - chunk.size) fuel
    goLength (n - min n sent.raw.size) 1000000
  | .chunked => do
    -- Read once, from where the prefix left off, holding no more than a line of the
    -- framing: the data is let go as it is relayed.  A request body is framed again
    -- (`sent.chunked`); a response is relayed as it arrived.
    let (start, reframe) ← match sent.chunked with
      | some r => pure (r, true)
      | none => match ({} : Http.Chunked.Reader).feed sent.raw with
        | .ok (r, none) => pure (r, false)
        | .ok (_, some _) => return ByteArray.empty
        | .error e => throw (IO.userError s!"malformed chunked body: {e}")
    if start.finished then return ByteArray.empty
    let rec goChunked (r : Http.Chunked.Reader) (fuel : Nat) : IO Bytes := do
      match fuel with
      | 0 => throw (IO.userError "the chunked body did not end")
      | fuel + 1 => do
        let chunk ← from_.read 65536
        if chunk.size == 0 then throw (IO.userError "the connection closed mid-body")
        match r.feed chunk with
        | .ok (r, some upTo) =>
          -- The body ends inside this read: relay up to the end and no further.
          to.write (if reframe then r.emitted else Bytes.take chunk upTo)
          return Bytes.drop chunk upTo
        | .error e => throw (IO.userError s!"malformed chunked body: {e}")
        | .ok (r, none) =>
          to.write (if reframe then r.emitted else chunk)
          goChunked r fuel
    goChunked { start with limit := 0, entity := ByteArray.empty } 1000000
  | .untilClose => do
    let rec goClose (fuel : Nat) : IO Bytes := do
      match fuel with
      | 0 => return ByteArray.empty
      | fuel + 1 => do
        let chunk ← from_.read 65536
        if chunk.size == 0 then return ByteArray.empty
        to.write chunk
        goClose fuel
    goClose 1000000

end Proxy
end Kleis
