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

/-- Decode the entity bytes available in `raw` under a framing. -/
private def entityOf (framing : Http.Framing) (raw : Bytes) (limit : Nat) :
    Except String (Bytes × Bool × Bool) :=
  match framing with
  | .empty => .ok (ByteArray.empty, true, true)
  | .length n =>
    let have_ := min raw.size n
    .ok (Bytes.take raw have_, have_ ≥ n, raw.size ≥ n)
  | .chunked =>
    match Http.Chunked.decode raw limit with
    | .done body _ complete => .ok (body, complete, complete)
    | .need => .ok (ByteArray.empty, false, false)
    | .error e => throw e
  | .untilClose => .ok (raw, false, false)

/-- Read from the client until the decoder is satisfied, the framing ends, or
the cap is reached.

`already` is whatever was read past the head while looking for it — a client
that pipelines the body into the same packet as the request line, which every
git client does.  Anything past the end of the body is returned as `excess`,
never as part of the body. -/
def readBodyPrefix (s : Net.Stream) (framing : Http.Framing) (decoder : Wire.Decoder)
    (already : Bytes) (cap : Nat) :
    IO (BodyPrefix × Option LeanBiscuit.Datalog.Value) := do
  if framing == .empty then return ({ BodyPrefix.empty with excess := already }, none)
  let rec go (received : Bytes) (fuel : Nat) :
      IO (BodyPrefix × Option LeanBiscuit.Datalog.Value) := do
    let (raw, excess) := splitAtFraming framing received
    let (entity, complete, framingDone) ← match entityOf framing raw cap with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"malformed request body: {e}")
    let seen : BodyPrefix := { raw, entity, complete, framingDone, excess }
    -- Ask the decoder what it makes of what we have.  An out-of-process
    -- decoder is only worth starting once, so it waits for the whole prefix.
    let verdict : Wire.Decoded := match decoder with
      | .pure d => d.step entity complete
      | .exec _ _ =>
        if complete || entity.size ≥ cap then .opaque else .need (entity.size + 1)
      | .opaque => .opaque
    match verdict with
    | .done value _ => return (seen, some value)
    | .opaque =>
      match decoder with
      | .exec command args => return (seen, ← Wire.runExec command args entity)
      | _ => return (seen, none)
    | .need atLeast =>
      if complete then return (seen, none)
      if entity.size ≥ cap || raw.size ≥ cap * 2 then
        -- Past the cap the body is relayed but not understood, and the
        -- authorizer's truncation guard turns that into a refusal for any
        -- policy that depended on it.
        return (seen, none)
      match fuel with
      | 0 => return (seen, none)
      | fuel + 1 => do
        let want := max 4096 (atLeast - entity.size)
        let chunk ← s.read (min want 65536)
        -- A client that goes away mid-body has sent a truncated request, which is
        -- not one to decide on or forward as if it were whole.
        if chunk.size == 0 then throw (IO.userError "the client closed mid-body")
        go (received ++ chunk) fuel
  go already 4096

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
    let rec goChunked (seen : Bytes) (fuel : Nat) : IO Bytes := do
      match fuel with
      | 0 => throw (IO.userError "the chunked body did not end")
      | fuel + 1 => do
        let chunk ← from_.read 65536
        if chunk.size == 0 then throw (IO.userError "the connection closed mid-body")
        let all := seen ++ chunk
        match Http.Chunked.scan all with
        | .done consumed =>
          -- The body ends inside this read: relay up to the end and no further.
          let upTo := consumed - seen.size
          to.write (Bytes.take chunk upTo)
          return Bytes.drop chunk upTo
        | .error e => throw (IO.userError s!"malformed chunked body: {e}")
        | .need =>
          to.write chunk
          goChunked all fuel
    goChunked sent.raw 1000000
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
