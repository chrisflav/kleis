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

/-- Write a refusal to the client.

Never throws: a client that has gone away cannot be told anything, and a refusal
that failed must not take the audit record written after it down with it — a
bearer could otherwise make credentialed requests and leave no trace simply by
closing the connection early. -/
def refuse (client : Net.Stream) (status : Nat) (requestId reason : String) : IO Unit := do
  let body := s!"kleis: {reason}\n\nrequest {requestId}\n"
  try
    client.write (Http.simpleResponse status "text/plain; charset=utf-8" body
      #[("x-kleis-request-id", requestId)])
  catch _ => pure ()

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
  /-- Whether this is the last request the connection will carry, so the response
  says `Connection: close` rather than leaving the client to find out. -/
  closeAfter : Bool := false

/-- What relaying a response came to. -/
structure Relayed where
  /-- The origin's status. -/
  status : Nat
  /-- Whether the response ended where its framing said and nothing followed it,
  so that the connection it came on is in a known state and may carry another
  request. -/
  clean : Bool
  /-- Whether the origin asked to close its connection. -/
  originCloses : Bool

/-- Relay a response from the origin to the client, streaming the body.

`none` when the origin closed before sending a single byte, which is what an
idle connection the origin has already given up on looks like.

Interim responses (`100 Continue`, `103 Early Hints`) are read and dropped.
The request was already relayed whole, so a `100` tells the client nothing, and
relaying one *as* the response would end the exchange before the real answer
arrived — a push large enough for git to send `Expect: 100-continue` would hang.
A `101 Switching Protocols` is relayed and ends the connection: the proxy
forwards no `Upgrade`, so an origin sending one is not one to keep talking to.

Nothing past the end of the response is relayed.  An origin that sent more than
one response's worth has a connection in a state nobody can account for, so it
is not pooled. -/
private def relayResponse (ctx : Context) (origin client : Net.Stream) (method : String)
    (requestId : String) (closeClient : Bool) (started : IO.Ref Bool) :
    IO (Option Relayed) := do
  let first ← origin.read 65536
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
  let (response, received) ← readHead first 4096
  let switching := response.status == 101
  let delimited := response.framing != .untilClose && !switching
  let originCloses := (Http.Headers.tokens response.headers "connection").contains "close"
    || response.version == "HTTP/1.0" || switching
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
  let (body, excess) := splitAtFraming response.framing received
  started.set true
  client.write (Http.writeResponse { response with headers })
  client.write body
  let sent : BodyPrefix :=
    { raw := body, entity := body
      complete := false
      framingDone := match response.framing with
        | .empty => true
        | .length n => body.size ≥ n
        | .chunked => match Http.Chunked.scan body with
          | .done _ => true
          | _ => false
        | .untilClose => false }
  let after ← relayBody origin client response.framing sent
  return some { status := response.status
                clean := delimited && excess.size == 0 && after.size == 0
                originCloses }

/-- Send a request on an origin connection, returning `false` if the
connection turned out to be dead before anything was written. -/
private def sendHead (origin : Net.Stream) (head : Bytes) (body : BodyPrefix) : IO Bool := do
  try
    origin.write head
    origin.write body.raw
    return true
  catch _ => return false

/-- Methods that may be sent a second time if the first attempt is in doubt. -/
private def idempotent (method : String) : Bool :=
  method == "GET" || method == "HEAD" || method == "OPTIONS"

/-- Send the request upstream and relay the answer.  Returns the status and
whether the client's connection may carry another request.

A connection to the same origin left idle by an earlier request is reused when
there is one, which matters for git: a clone is a handful of requests, and each
one paying for a new TLS handshake with the origin is most of what it costs.  A
reused connection may have been closed by the origin in the meantime, so only a
request that is safe to send twice goes on one — a `GET`, `HEAD` or `OPTIONS`
whose whole body is in hand — and is sent again on a fresh connection if the old
one closes before answering.  Everything else gets a fresh connection: a `POST`
the origin acted on before dropping the connection must not be acted on twice.

`started` is set once any of the response has been written to the client, so a
caller handling a failure knows whether an error response can still be sent. -/
private def sendUpstream (ctx : Context) (job : Job) (outgoing : Model.Request)
    (body : BodyPrefix) (requestId : String) (started : IO.Ref Bool)
    (allow : Option (Std.Net.SocketAddress → Bool) := none) :
    IO (Option Nat × Bool) := do
  let key := s!"{outgoing.scheme}://{outgoing.host}:{outgoing.port}"
  -- A connection checked against `allow` is not put in the pool, where a request
  -- that was not checked could pick it up.
  let pooling := ctx.config.upstreamIdleSeconds > 0 && allow.isNone
  let clientCloses := (Http.Headers.tokens job.wire.headers "connection").contains "close"
    || job.wire.version == "HTTP/1.0" || job.closeAfter
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
    Net.openOrigin ctx.clientCtx outgoing.scheme outgoing.host (UInt16.ofNat outgoing.port) allow
  -- What the client sent past the end of this request's body, if anything: a
  -- pipelined request.  It is not relayed, and the client's connection is closed
  -- after this response so that it sends it again rather than have it lost.
  let clientExcess ← IO.mkRef body.excess
  -- One attempt on one connection: `none` if it was dead before answering.
  let attempt (origin : Net.Stream) : IO (Option Relayed) := do
    if !(← sendHead origin head body) then return none
    let after ← relayBody job.client origin job.wire.framing body
    if after.size > 0 then clientExcess.set after
    -- A client whose pipelined bytes were dropped is told the connection ends here, so it
    -- sends that request again rather than wait for an answer that is not coming.
    relayResponse ctx origin job.client outgoing.method requestId
      (clientCloses || (← clientExcess.get).size > 0) started
  let retryable := idempotent outgoing.method && body.framingDone
  let pooled ← if pooling && retryable then ctx.pool.take? key else pure none
  let viaFresh : IO (Net.Stream × Relayed) := do
    let fresh ← openFresh
    match ← (try attempt fresh catch e => do fresh.close; throw e) with
    | some r => pure (fresh, r)
    | none => do fresh.close; throw (IO.userError "the origin closed before responding")
  let (origin, relayed) ← match pooled with
    | some origin => do
      -- Only a clean end before any answer counts as a dead idle connection; a
      -- read error after the request went out is not evidence the origin did not
      -- act on it.
      let r ← try attempt origin catch e => do origin.close; throw e
      match r with
      | some r => pure (origin, r)
      | none => do origin.close; viaFresh
    | none => viaFresh
  if pooling && relayed.clean && !relayed.originCloses then
    ctx.pool.put key origin
  else origin.close
  let more := relayed.clean && !clientCloses && (← clientExcess.get).size == 0
  return (some relayed.status, more)

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
  if !ctx.config.passesPort bare.port then
    refuse job.client 403 requestId s!"passthrough is not allowed to port {bare.port}"
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
  let started ← IO.mkRef false
  let (status, more) ← try
      sendUpstream ctx job outgoing body requestId started
        (allow := some fun a => ctx.config.passthroughInternal || !Net.Tcp.isInternal a)
    catch e => do
      if ctx.config.audit then
        ctx.audit.append { record with outcome := s!"passthrough, upstream failure: {e}" }
      if !(← started.get) then
        refuse job.client 502 requestId s!"the origin could not be reached: {e}"
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
          if request.scheme != "https" && !manifest.credential.allowPlaintext then
            throw (IO.userError s!"the credential `{credentialName}` is only sent over https")
          if manifest.mayCredentialReach request.host then do
            let declared ← ctx.declared.get
            let some credentialRecord ← match declared.find? (·.name == credentialName) with
                | some r => pure (some r)
                | none => Credential.load? credentialName
              | throw (IO.userError (Policy.Rejection.noCredential credentialName).toString)
            -- A grant naming a credential of another service — a typo in a route — must
            -- not send, say, a cloud key to GitHub.
            if credentialRecord.service != manifest.name then
              throw (IO.userError s!"the credential `{credentialName}` is for `{credentialRecord.service}`, not `{manifest.name}`")
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
    -- The audit record first: the request has gone upstream on a credential, and
    -- that is recorded whatever happens to the client.  An error response only if
    -- the client has seen none of a response yet; otherwise it would be written
    -- into the middle of a body.
    let started ← IO.mkRef false
    let (status, more) ← try
        sendUpstream ctx job outgoing body requestId started
      catch e => do
        if ctx.config.audit then
          ctx.audit.append { auditRecord with outcome := s!"upstream failure: {e}" }
        if !(← started.get) then
          refuse job.client 502 requestId s!"the origin could not be reached: {e}"
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
