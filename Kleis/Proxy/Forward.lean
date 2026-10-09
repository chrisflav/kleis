import Kleis.Proxy.Context
import Kleis.Proxy.Body
import Kleis.Credential.Secret
import Kleis.Http.Writer
import Kleis.Net.Client
import Kleis.Policy.Select

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
open LeanBiscuit.Token (Biscuit AuthorizerBuilder Authorizer)

/-- Write a refusal to the client. -/
def refuse (client : Net.Stream) (status : Nat) (requestId reason : String) : IO Unit := do
  let body := s!"kleis: {reason}\n\nrequest {requestId}\n"
  client.write (Http.simpleResponse status "text/plain; charset=utf-8" body
    #[("x-kleis-request-id", requestId)])

/-- Does the token still hold — unrevoked, unexpired, its own checks passing?

The same evaluation a proxied request gets, minus a grant: a token's checks are
the bearer's, and an expired issuer credential must stop working here exactly
as an expired bearer token stops working at the proxy. -/
def tokenHolds (ctx : Context) (token : Biscuit) : IO (Except String Unit) := do
  let revoked := (← ctx.revocations.get).ids
  let ids := (Biscuit.revocationIdentifiers token).map Bytes.toHex
  if ids.any revoked.contains then return .error "the token is revoked"
  let now ← Store.now
  let builder : AuthorizerBuilder := {
    facts := [⟨⟨"time", [.date now]⟩⟩]
    rules := [], checks := [], scopes := []
    policies := [{ queries := [{ head := ⟨"query", []⟩, body := [], expressions := []
                                 scopes := [] }], kind := .allow }]
    externs := Policy.standard, limits := {} }
  match Authorizer.build builder token with
  | .error e => return .error (TokenError.toString e)
  | .ok a =>
    match (Authorizer.authorizeWithState a).1 with
    | .ok _ => return .ok ()
    | .error e => return .error (TokenError.toString e)

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

/-- What relaying a response came to. -/
structure Relayed where
  /-- The origin's status. -/
  status : Nat
  /-- Whether the response ended where its framing said, so that the
  connection it came on is in a known state and may carry another request. -/
  delimited : Bool
  /-- Whether the origin asked to close its connection. -/
  originCloses : Bool

/-- Relay a response from the origin to the client, streaming the body.

`none` when the origin closed before sending a single byte, which is what an
idle connection the origin has already given up on looks like, and the one
failure a request may be retried after: nothing has reached the client yet.

Interim responses (`100 Continue`, `103 Early Hints`) are read and dropped.
The request was already relayed whole, so a `100` tells the client nothing, and
relaying one *as* the response would end the exchange before the real answer
arrived — a push large enough for git to send `Expect: 100-continue` would hang. -/
private def relayResponse (ctx : Context) (origin client : Net.Stream) (method : String)
    (requestId : String) (closeClient : Bool) : IO (Option Relayed) := do
  let first ← try origin.read 65536 catch _ => pure ByteArray.empty
  if first.size == 0 then return none
  let rec readHead (buf : Bytes) (fuel : Nat) : IO (Http.Response × Bytes) := do
    match fuel with
    | 0 => throw (IO.userError "the origin's response head never ended")
    | fuel + 1 =>
      match Http.readResponse buf method { maxHeadSize := ctx.config.maxHeadSize } with
      | .done r consumed =>
        if 100 ≤ r.status && r.status < 200 && r.status != 101 then
          readHead (Bytes.drop buf consumed) fuel
        else pure (r, Bytes.drop buf consumed)
      | .error e => throw (IO.userError s!"the origin sent a malformed response: {e}")
      | .need => do
        let chunk ← origin.read 65536
        if chunk.size == 0 then throw (IO.userError "the origin closed mid-response")
        readHead (buf ++ chunk) fuel
  let (response, rest) ← readHead first 4096
  let delimited := response.framing != .untilClose
  let originCloses := (Http.Headers.tokens response.headers "connection").contains "close"
    || response.version == "HTTP/1.0"
  -- The hop-by-hop fields belong to the connection with the origin, not to the
  -- one with the client, and the request identifier is added so that a bearer
  -- can quote it.
  let headers := (Http.stripHopByHop response.headers)
    |> (Http.Headers.set · "x-kleis-request-id" requestId)
  let headers := match response.framing with
    | .chunked => Http.Headers.set headers "transfer-encoding" "chunked"
    | _ => headers
  -- A body that ends only when the connection does cannot be followed by
  -- another response on it, and the client has to be told.
  let headers := if closeClient || !delimited then Http.Headers.set headers "connection" "close"
    else headers
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
  return some { status := response.status, delimited, originCloses }

/-- Send a request on an origin connection, returning `false` if the
connection turned out to be dead before anything was written. -/
private def sendHead (origin : Net.Stream) (head : Bytes) (body : BodyPrefix) : IO Bool := do
  try
    origin.write head
    origin.write body.raw
    return true
  catch _ => return false

/-- Send the request upstream and relay the answer.  Returns the status and
whether the client's connection may carry another request.

A connection to the same origin left idle by an earlier request is reused when
there is one, which matters for git: a clone is a handful of requests, and each
one paying for a new TLS handshake with the origin is most of what it costs.  A
reused connection may have been closed by the origin in the meantime, so a
request goes on one only when its whole body is in hand and can be sent again on
a fresh connection if the old one turns out to be dead; a request still
streaming its body from the client always gets a fresh one. -/
private def sendUpstream (ctx : Context) (job : Job) (outgoing : Model.Request)
    (body : BodyPrefix) (requestId : String) : IO (Option Nat × Bool) := do
  let key := s!"{outgoing.scheme}://{outgoing.host}:{outgoing.port}"
  let pooling := ctx.config.upstreamIdleSeconds > 0
  let clientCloses := (Http.Headers.tokens job.wire.headers "connection").contains "close"
    || job.wire.version == "HTTP/1.0"
  -- `Expect` is dropped as well as the hop-by-hop fields: the proxy already
  -- holds the start of the body and relays the rest unasked, so an origin's
  -- `100 Continue` would only be one more response to throw away.
  let headers := (Http.stripHopByHop outgoing.headers)
    |> (Http.Headers.remove · "expect")
    |> (Http.Headers.set · "host" outgoing.authority)
    |> (fun h => if pooling then h else Http.Headers.set h "connection" "close")
  let head := Http.writeRequest {
    method := outgoing.method, target := outgoing.originTarget
    version := "HTTP/1.1", headers, framing := job.wire.framing }
  let openFresh : IO Net.Stream :=
    Net.openOrigin ctx.clientCtx outgoing.scheme outgoing.host (UInt16.ofNat outgoing.port)
  -- One attempt on one connection: `none` if it was dead before answering.
  let attempt (origin : Net.Stream) : IO (Option Relayed) := do
    if !(← sendHead origin head body) then return none
    relayBody job.client origin job.wire.framing body
    relayResponse ctx origin job.client outgoing.method requestId clientCloses
  let pooled ← if pooling && body.framingDone then ctx.pool.take? key
    else pure none
  let (origin, relayed) ← match pooled with
    | some origin => do
      match ← (try attempt origin catch e => do origin.close; throw e) with
      | some r => pure (origin, r)
      | none =>
        origin.close
        let fresh ← openFresh
        match ← (try attempt fresh catch e => do fresh.close; throw e) with
        | some r => pure (fresh, r)
        | none => do fresh.close; throw (IO.userError "the origin closed before responding")
    | none => do
      let fresh ← openFresh
      match ← (try attempt fresh catch e => do fresh.close; throw e) with
      | some r => pure (fresh, r)
      | none => do fresh.close; throw (IO.userError "the origin closed before responding")
  if pooling && relayed.delimited && !relayed.originCloses then
    ctx.pool.put key origin
  else origin.close
  return (some relayed.status, relayed.delimited && !clientCloses)

/-- Forward a request for a host no manifest claims, which the configuration's
`passthrough` lets through: no policy, no credential, nothing stripped but the
proxy's own header.  The client's own `Authorization` is left alone — it is a
credential for that host which the client already holds, not one of ours.

The token is still checked for revocation and expiry, so that revoking a job's
token ends everything it can do through this proxy, passthrough included. -/
private def forwardBlind (ctx : Context) (job : Job) (bare : Model.Request)
    (requestId : String) (now : Nat) : IO Bool := do
  if let .error e ← tokenHolds ctx job.token then
    refuse job.client 407 requestId s!"the token was not accepted: {e}"
    return false
  let (body, _) ← try
      readBodyPrefix job.client job.wire.framing .opaque job.pipelined 0
    catch e => do
      refuse job.client 400 requestId (toString e)
      return false
  let outgoing := { bare with
    headers := Http.Headers.removeAll bare.headers ["proxy-authorization", "x-kleis-token"] }
  let record : AuditRecord := {
    time := now, requestId, method := bare.method, url := bare.url
    clientIp := job.clientIp, service := "passthrough", manifestVersion := ""
    grant := "", grantVersion := ""
    revocationIds := (Biscuit.revocationIdentifiers job.token).map Bytes.toHex
    allowed := true, outcome := "passthrough", facts := []
    credential := none, status := none }
  let (status, more) ← try
      sendUpstream ctx job outgoing body requestId
    catch e => do
      refuse job.client 502 requestId s!"the origin could not be reached: {e}"
      if ctx.config.audit then
        ctx.audit.append { record with outcome := s!"passthrough, upstream failure: {e}" }
      return false
  if ctx.config.audit then ctx.audit.append { record with status }
  return more

/-- Forward one request.  Returns whether the connection may carry another. -/
def forward (ctx : Context) (job : Job) : IO Bool := do
  let requestId ← ctx.nextRequestId
  let registry ← ctx.registry.get
  let now ← Store.now

  -- Build the normalized request, without a body yet.
  let bare ← match Model.Request.ofWire job.wire job.scheme job.tunnel ByteArray.empty true with
    | .ok r => pure r
    | .error e => do refuse job.client 400 requestId e; return false

  -- Which service, and which of the token's grants may decide for it.
  let result : Except Policy.Rejection (Service.Manifest × List Policy.Grant) :=
    match registry.forHost? bare.host with
    | none => .error (.unknownHost bare.host)
    | some manifest => do
      let grants ← Policy.candidates registry job.token manifest bare.host
      pure (manifest, grants)
  let (manifest, grants) ← match result with
    | .error (.unknownHost host) => do
      if ctx.config.passes host then return (← forwardBlind ctx job bare requestId now)
      else
        refuse job.client 403 requestId (Policy.Rejection.unknownHost host).toString
        if ctx.config.audit then
          ctx.audit.append {
            time := now, requestId, method := bare.method, url := bare.url
            clientIp := job.clientIp, service := "", manifestVersion := ""
            grant := ",".intercalate (Token.grantsOf job.token), grantVersion := ""
            revocationIds := (Biscuit.revocationIdentifiers job.token).map Bytes.toHex
            allowed := false, outcome := (Policy.Rejection.unknownHost host).toString
            facts := [], credential := none, status := none }
        return false
    | .error r => do
      refuse job.client 403 requestId r.toString
      -- An audit record even here: a request that never reached a policy is
      -- still a request somebody made with a valid token.
      if ctx.config.audit then
        ctx.audit.append {
          time := now, requestId, method := bare.method, url := bare.url
          clientIp := job.clientIp, service := "", manifestVersion := ""
          grant := ",".intercalate (Token.grantsOf job.token), grantVersion := ""
          revocationIds := (Biscuit.revocationIdentifiers job.token).map Bytes.toHex
          allowed := false, outcome := r.toString, facts := []
          credential := none, status := none }
      return false
    | .ok v => pure v

  -- Read as much of the body as the decoder wants.
  let decoder := manifest.decoderFor (Http.Headers.find? job.wire.headers "content-type") bare
  let cap := min manifest.maxDecodePrefix ctx.config.maxDecodePrefix
  let (body, decoded) ← try
      readBodyPrefix job.client job.wire.framing decoder job.pipelined cap
    catch e => do
      refuse job.client 400 requestId (toString e)
      return false

  let request := { bare with
    bodyPrefix := body.entity, bodyComplete := body.complete
    bodySize := match job.wire.framing with | .length n => some n | _ => none }

  -- Decide, one grant at a time.
  let revocations ← ctx.revocations.get
  let remembered ← ctx.memory.factsFor job.token
  let choice := Policy.choose grants fun grant => {
    request
    body := Policy.Body.classify decoder.configured (job.wire.framing != .empty) decoded
    manifest, grant, token := job.token, revoked := revocations.ids
    now, clientIp := job.clientIp, requestId, remembered }
  let grant := choice.grant
  let outcome := choice.outcome

  let mut auditRecord : AuditRecord := {
    time := now, requestId, method := request.method, url := request.url
    clientIp := job.clientIp, service := manifest.name
    manifestVersion := manifest.version, grant := grant.name
    grantVersion := grant.version, revocationIds := outcome.revocationIds
    allowed := outcome.allowed, outcome := choice.reason, facts := outcome.facts
    credential := none, status := none }

  match outcome.authorized with
  | none => do
    refuse job.client 403 requestId choice.reason
    -- A refusal is the thing an operator most often has to explain, so the
    -- facts behind one can be turned on without turning on everything.
    if (← IO.getEnv "KLEIS_DEBUG_FACTS").isSome then
      for f in outcome.facts do
        let h ← IO.getStderr
        h.putStrLn s!"kleis: {requestId}: fact {f}"
      (← IO.getStderr).flush
    if ctx.config.audit then ctx.audit.append auditRecord
    return false
  | some authorized => do
    -- Attach the credential.  This is the only place a secret is read, and it
    -- needs the value the authorizer produced.
    let outgoing ← try
        match authorized.credential with
        | some credentialName =>
          if manifest.mayCredentialReach request.host then do
            let some credentialRecord ← Credential.load? credentialName
              | throw (IO.userError (Policy.Rejection.noCredential credentialName).toString)
            let secret ← Credential.resolve ctx.credentials ctx.clientCtx credentialRecord
              grant.narrow
            auditRecord := { auditRecord with
              credential := some (credentialName, secret.fingerprint) }
            match Credential.bind authorized secret with
            | .ok r => pure r
            | .error e => throw (IO.userError e.toString)
          else
            -- A host the manifest claims but the credential is not bound to is
            -- proxied without it, rather than refused: the request is still the
            -- client's to make, it just does not get to spend anything.
            pure (Credential.stripOnly authorized)
        -- A grant that chose no credential for this request — an anonymous
        -- grant, or a route to none — forwards what the client sent, minus
        -- anything that could carry a credential of its own.
        | none => pure (Credential.stripOnly authorized)
      catch e => do
        refuse job.client 502 requestId s!"the credential could not be obtained: {e}"
        if ctx.config.audit then
          ctx.audit.append { auditRecord with allowed := false, outcome := toString e }
        return false

    -- Forward.
    let (status, more) ← try
        sendUpstream ctx job outgoing body requestId
      catch e => do
        refuse job.client 502 requestId s!"the origin could not be reached: {e}"
        if ctx.config.audit then
          ctx.audit.append { auditRecord with outcome := s!"upstream failure: {e}" }
        return false

    -- What a route asked to be remembered once this succeeded: the repository a
    -- token created, so that the same token may push to it next.  Only on a 2xx,
    -- so a creation GitHub refused leaves nothing behind.
    if let some s := status then
      if 200 ≤ s && s < 300 then
        let facts := manifest.remember request decoded
        if !facts.isEmpty then ctx.memory.add job.token facts
    if ctx.config.audit then ctx.audit.append { auditRecord with status }
    -- The client's connection carries another request when this one ended
    -- where its framing said; a refusal always closes it (`Http.simpleResponse`).
    return more

end Proxy
end Kleis
