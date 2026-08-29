import Auth.Http.Chunked
import Auth.Wire.Exec
import Auth.Net.Stream

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

namespace Auth
namespace Proxy

open LeanBiscuit (Bytes)

/-- What was read of a body. -/
structure BodyPrefix where
  /-- The bytes as they arrived, framing included. -/
  raw : Bytes
  /-- The entity bytes, framing removed. -/
  entity : Bytes
  /-- Whether `entity` is the whole body. -/
  complete : Bool
  /-- Whether the framing has been consumed to its end, so that nothing more
  need be relayed. -/
  framingDone : Bool
  deriving Inhabited

/-- Nothing at all. -/
def BodyPrefix.empty : BodyPrefix :=
  { raw := ByteArray.empty, entity := ByteArray.empty, complete := true, framingDone := true }

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
git client does. -/
def readBodyPrefix (s : Net.Stream) (framing : Http.Framing) (decoder : Wire.Decoder)
    (already : Bytes) (cap : Nat) :
    IO (BodyPrefix × Option LeanBiscuit.Datalog.Value) := do
  if framing == .empty then return (BodyPrefix.empty, none)
  let rec go (raw : Bytes) (fuel : Nat) :
      IO (BodyPrefix × Option LeanBiscuit.Datalog.Value) := do
    let (entity, complete, framingDone) ← match entityOf framing raw cap with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"malformed request body: {e}")
    let seen : BodyPrefix := { raw, entity, complete, framingDone }
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
        if chunk.size == 0 then
          return ({ seen with complete := true, framingDone := true }, none)
        go (raw ++ chunk) fuel
  go already 4096

/-- Relay the rest of a body from the client to the origin.

Nothing is buffered: a chunk is read and written, and the loop ends when the
framing says the body is over. -/
def relayBody (from_ to : Net.Stream) (framing : Http.Framing) (sent : BodyPrefix) :
    IO Unit := do
  if sent.framingDone then return ()
  match framing with
  | .empty => return ()
  | .length n => do
    let rec goLength (remaining : Nat) (fuel : Nat) : IO Unit := do
      if remaining == 0 then return ()
      match fuel with
      | 0 => throw (IO.userError "the request body did not end")
      | fuel + 1 => do
        let chunk ← from_.read (min remaining 65536)
        if chunk.size == 0 then throw (IO.userError "the client closed mid-body")
        to.write chunk
        goLength (remaining - chunk.size) fuel
    goLength (n - min n sent.raw.size) 1000000
  | .chunked => do
    let rec goChunked (seen : Bytes) (fuel : Nat) : IO Unit := do
      match Http.Chunked.scan seen with
      | .done _ => return ()
      | .error e => throw (IO.userError s!"malformed chunked body: {e}")
      | .need =>
        match fuel with
        | 0 => throw (IO.userError "the chunked body did not end")
        | fuel + 1 => do
          let chunk ← from_.read 65536
          if chunk.size == 0 then throw (IO.userError "the client closed mid-body")
          to.write chunk
          -- Only the framing is retained, and only as far as the scanner
          -- needs: the payload is written out and dropped.
          goChunked (seen ++ chunk) fuel
    goChunked sent.raw 1000000
  | .untilClose => do
    let rec goClose (fuel : Nat) : IO Unit := do
      match fuel with
      | 0 => return ()
      | fuel + 1 => do
        let chunk ← from_.read 65536
        if chunk.size == 0 then return ()
        to.write chunk
        goClose fuel
    goClose 1000000

end Proxy
end Auth
