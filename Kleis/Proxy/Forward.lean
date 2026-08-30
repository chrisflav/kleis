import Kleis.Proxy.Context
import Kleis.Proxy.Body
import Kleis.Credential.Secret
import Kleis.Http.Writer
import Kleis.Net.Client

/-!
# One request, end to end

Read the body prefix, turn everything into facts, decide, attach the
credential, forward, relay the answer, write the audit record.

The order is not negotiable and the types say so: `Credential.bind` takes an
`AuthorizedRequest`, and the only thing that makes one is the authorizer.  So
the sequence below cannot be rearranged into one that spends a credential
first, however it is edited.

## What a refusal looks like

A refusal quotes the checks that failed and the request identifier.  A bearer
who cannot see *why* a push was refused will retry it, and then ask a human;
telling them `check all ref_update($ref), $ref.starts_with("refs/heads/dev/")`
failed answers the question without anybody being paged.  It gives away only
what the bearer's own grant already says.
-/

namespace Kleis
namespace Proxy

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- Why a request never reached a policy decision. -/
inductive Rejection where
  /-- No manifest claims the host. -/
  | unknownHost (host : String)
  /-- The token names a grant nobody has. -/
  | unknownGrant (name : String)
  /-- The token names no grant at all. -/
  | noGrant
  /-- The grant is for a different service than the host belongs to. -/
  | wrongService (grant service host : String)
  /-- The credential the grant spends is not installed. -/
  | noCredential (name : String)

/-- Describe a rejection. -/
def Rejection.toString : Rejection → String
  | .unknownHost h => s!"no service manifest claims `{h}`"
  | .unknownGrant n => s!"the token names the grant `{n}`, which is not configured"
  | .noGrant => "the token names no grant"
  | .wrongService g s h =>
    s!"the grant `{g}` is for the service `{s}`, which does not claim `{h}`"
  | .noCredential n => s!"the credential `{n}` is not installed"

/-- Write a refusal to the client. -/
def refuse (client : Net.Stream) (status : Nat) (requestId reason : String) : IO Unit := do
  let body := s!"kleis: {reason}\n\nrequest {requestId}\n"
  client.write (Http.simpleResponse status "text/plain; charset=utf-8" body
    #[("x-kleis-request-id", requestId)])

/-- Everything needed to forward one request. -/
structure Job where
  /-- The client's stream. -/
  client : Net.Stream
  /-- The wire request. -/
  wire : Http.Request
  /-- Bytes read past the head, which are the start of the body. -/
  pipelined : Bytes
  /-- `http` or `https`, as the client sees it. -/
  scheme : String
  /-- The authority a `CONNECT` established, if any. -/
  tunnel : Option (String × Nat)
  /-- The bearer's verified token. -/
  token : Biscuit
  /-- The client's address. -/
  clientIp : String

/-- Relay a response from the origin to the client, streaming the body. -/
private def relayResponse (ctx : Context) (origin client : Net.Stream) (method : String)
    (requestId : String) : IO (Option Nat) := do
  let rec readHead (buf : Bytes) (fuel : Nat) : IO (Http.Response × Bytes) := do
    match fuel with
    | 0 => throw (IO.userError "the origin's response head never ended")
    | fuel + 1 =>
      match Http.readResponse buf method { maxHeadSize := ctx.config.maxHeadSize } with
      | .done r consumed => pure (r, Bytes.drop buf consumed)
      | .error e => throw (IO.userError s!"the origin sent a malformed response: {e}")
      | .need => do
        let chunk ← origin.read 65536
        if chunk.size == 0 then throw (IO.userError "the origin closed before responding")
        readHead (buf ++ chunk) fuel
  let (response, rest) ← readHead ByteArray.empty 4096
  -- The hop-by-hop fields belong to the connection with the origin, not to the
  -- one with the client, and the request identifier is added so that a bearer
  -- can quote it.
  let headers := (Http.stripHopByHop response.headers)
    |> (Http.Headers.set · "x-kleis-request-id" requestId)
  let headers := match response.framing with
    | .chunked => Http.Headers.set headers "transfer-encoding" "chunked"
    | _ => headers
  client.write (Http.writeResponse { response with headers })
  client.write rest
  let sent : BodyPrefix :=
    { raw := rest, entity := rest
      complete := false
      framingDone := match response.framing with
        | .empty => true
        | .length n => rest.size ≥ n
        | _ => false }
  relayBody origin client response.framing sent
  return some response.status

/-- Open a connection to the origin, send the request, and relay the answer.

Separate from `forward` so that the connection is closed on every path out of
it, including the ones that throw. -/
private def sendUpstream (ctx : Context) (job : Job) (outgoing : Model.Request)
    (body : BodyPrefix) (requestId : String) : IO (Option Nat) := do
  let origin ← Net.openOrigin ctx.clientCtx outgoing.scheme outgoing.host
    (UInt16.ofNat outgoing.port)
  try
    let headers := (Http.stripHopByHop outgoing.headers)
      |> (Http.Headers.set · "host" outgoing.authority)
      |> (Http.Headers.set · "connection" "close")
    let head := Http.writeRequest {
      method := outgoing.method, target := outgoing.originTarget
      version := "HTTP/1.1", headers, framing := job.wire.framing }
    origin.write head
    origin.write body.raw
    relayBody job.client origin job.wire.framing body
    let status ← relayResponse ctx origin job.client outgoing.method requestId
    origin.close
    return status
  catch e =>
    origin.close
    throw e

/-- Forward one request.  Returns whether the connection may carry another. -/
def forward (ctx : Context) (job : Job) : IO Bool := do
  let requestId ← ctx.nextRequestId
  let registry ← ctx.registry.get
  let now ← Store.now

  -- Build the normalized request, without a body yet.
  let bare ← match Model.Request.ofWire job.wire job.scheme job.tunnel ByteArray.empty true with
    | .ok r => pure r
    | .error e => do refuse job.client 400 requestId e; return false

  -- Which service, which grant, which credential.
  let result : Except Rejection (Service.Manifest × Policy.Grant × Credential.Record) ← do
    match registry.forHost? bare.host with
    | none => pure (.error (.unknownHost bare.host))
    | some manifest =>
      match Token.grantOf? job.token with
      | none => pure (.error .noGrant)
      | some grantName =>
        match registry.grant? grantName with
        | none => pure (.error (.unknownGrant grantName))
        | some grant =>
          if grant.service != manifest.name then
            pure (.error (.wrongService grant.name grant.service bare.host))
          else
            match ← Credential.load? grant.credential with
            | none => pure (.error (.noCredential grant.credential))
            | some record => pure (.ok (manifest, grant, record))
  let (manifest, grant, credentialRecord) ← match result with
    | .error r => do
      refuse job.client 403 requestId r.toString
      -- An audit record even here: a request that never reached a policy is
      -- still a request somebody made with a valid token.
      if ctx.config.audit then
        auditAppend {
          time := now, requestId, method := bare.method, url := bare.url
          clientIp := job.clientIp, service := "", manifestVersion := ""
          grant := (Token.grantOf? job.token).getD "", grantVersion := ""
          revocationIds := (Biscuit.revocationIdentifiers job.token).map Bytes.toHex
          allowed := false, outcome := r.toString, facts := []
          credential := none, status := none }
      return false
    | .ok v => pure v

  -- Read as much of the body as the decoder wants.
  let decoder := manifest.decoderFor (Http.Headers.find? job.wire.headers "content-type")
  let cap := min manifest.maxDecodePrefix ctx.config.maxDecodePrefix
  let (body, decoded) ← try
      readBodyPrefix job.client job.wire.framing decoder job.pipelined cap
    catch e => do
      refuse job.client 400 requestId (toString e)
      return false

  let request := { bare with
    bodyPrefix := body.entity, bodyComplete := body.complete
    bodySize := match job.wire.framing with | .length n => some n | _ => none }

  -- Decide.
  let revocations ← ctx.revocations.get
  let outcome := Policy.run {
    request
    body := Policy.Body.classify decoder.configured (job.wire.framing != .empty) decoded
    manifest, grant, token := job.token, revoked := revocations.ids
    now, clientIp := job.clientIp, requestId }

  let mut auditRecord : AuditRecord := {
    time := now, requestId, method := request.method, url := request.url
    clientIp := job.clientIp, service := manifest.name
    manifestVersion := manifest.version, grant := grant.name
    grantVersion := grant.version, revocationIds := outcome.revocationIds
    allowed := outcome.allowed, outcome := outcome.reason, facts := outcome.facts
    credential := none, status := none }

  match outcome.authorized with
  | none => do
    refuse job.client 403 requestId outcome.reason
    -- A refusal is the thing an operator most often has to explain, so the
    -- facts behind one can be turned on without turning on everything.
    if (← IO.getEnv "KLEIS_DEBUG_FACTS").isSome then
      for f in outcome.facts do
        let h ← IO.getStderr
        h.putStrLn s!"kleis: {requestId}: fact {f}"
      (← IO.getStderr).flush
    if ctx.config.audit then auditAppend auditRecord
    return false
  | some authorized => do
    -- Attach the credential.  This is the only place a secret is read, and it
    -- needs the value the authorizer produced.
    let outgoing ← try
        if manifest.mayCredentialReach request.host then do
          let secret ← Credential.resolve ctx.credentials ctx.clientCtx credentialRecord
            grant.narrow
          auditRecord := { auditRecord with
            credential := some (grant.credential, secret.fingerprint) }
          match Credential.bind authorized secret with
          | .ok r => pure r
          | .error e => throw (IO.userError e.toString)
        else
          -- A host the manifest claims but the credential is not bound to is
          -- proxied without it, rather than refused: the request is still the
          -- client's to make, it just does not get to spend anything.
          pure (Credential.stripOnly authorized)
      catch e => do
        refuse job.client 502 requestId s!"the credential could not be obtained: {e}"
        if ctx.config.audit then
          auditAppend { auditRecord with allowed := false, outcome := toString e }
        return false

    -- Forward.
    let status ← try
        sendUpstream ctx job outgoing body requestId
      catch e => do
        refuse job.client 502 requestId s!"the origin could not be reached: {e}"
        if ctx.config.audit then
          auditAppend { auditRecord with outcome := s!"upstream failure: {e}" }
        return false

    if ctx.config.audit then auditAppend { auditRecord with status }
    -- One request per upstream connection in this version, so the client's
    -- connection is closed with it rather than left in a state the origin no
    -- longer shares.
    return false

end Proxy
end Kleis
