import Std.Internal.UV.Timer
import Kleis.Proxy.Admin
import Kleis.Net.ClientHello
import Kleis.Net.TlsStream
import Kleis.Net.Socket

/-!
# One client connection

Three shapes of request arrive here, and the difference is the interception
mode rather than anything the policy layer sees:

- `CONNECT host:443` — the client thinks it is opening a tunnel.  A certificate
  for the name in the ClientHello is minted, TLS is terminated, and the
  requests inside are read as normal.
- an absolute-form target — an ordinary forward proxy request, which is what a
  plain `http://` URL through `HTTPS_PROXY` looks like.
- `/<scheme>/<host>/<path>` — rewrite mode, where the client was configured to
  send real URLs to the loopback with the origin in the path.  No TLS server,
  no certificate, nothing to install.

## Where the bearer's token comes from

`Proxy-Authorization`, in either the `Bearer` or the `Basic` form, because
those are what the tools can be made to send: git takes credentials in the
proxy URL and turns them into `Basic`, and everything else honours `Bearer`.
`X-Kleis-Token` exists for `http.extraHeader`.

On a `CONNECT` the header is on the tunnel request, and the requests inside it
have none — so the token is captured once and carried.  Whatever the client
sends inside is stripped, so a bearer cannot upgrade themselves mid-tunnel.
-/

namespace Kleis
namespace Proxy

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- The token a client presented, from whichever header carried it. -/
def bearerFrom? (headers : Http.Headers) : Option String :=
  let fromAuth (value : String) : Option String :=
    if value.startsWith "Bearer " || value.startsWith "bearer " then
      some (Str.trim (Str.stripPrefix (Str.stripPrefix value "Bearer ") "bearer "))
    else if value.startsWith "Basic " || value.startsWith "basic " then do
      let encoded := Str.trim (Str.stripPrefix (Str.stripPrefix value "Basic ") "basic ")
      let decoded ← Base64.decode? encoded
      let text := Bytes.toStringLossy decoded
      -- `user:password`; the token may be either half, since a proxy URL is
      -- written both ways in the wild.
      match Str.splitOnce? text ":" with
      | some (user, password) => some (if password.isEmpty then user else password)
      | none => some text
    else none
  match Http.Headers.find? headers "proxy-authorization" with
  | some v => fromAuth v
  | none =>
    match Http.Headers.find? headers "x-kleis-token" with
    | some v => some (Str.trim v)
    | none => (Http.Headers.find? headers "authorization").bind fromAuth

/-- Read one request head from a stream, returning it and whatever was read
past it. -/
def readHead (s : Net.Stream) (limits : Http.Limits) (already : Bytes)
    (timeoutSeconds : Nat := 30) : IO (Option (Http.Request × Bytes)) := do
  -- A client that opens a connection and sends no request — or not all of one —
  -- would hold a thread and a descriptor for as long as it liked.  A libuv timer
  -- closes the stream if the head has not arrived in time, which wakes the read
  -- below.  A timer rather than a sleeping task: it costs no thread while it waits,
  -- and stopping it when the head arrives drops its hold on the stream at once —
  -- a sleeping task would keep both for the whole timeout on every connection,
  -- which anyone able to connect could use to exhaust them.
  if timeoutSeconds == 0 then return ← go already 4096
  let timer ← Std.Internal.UV.Timer.mk (UInt64.ofNat (timeoutSeconds * 1000)) false
  let fired ← timer.next
  -- The callback may run on libuv's own loop, where waiting for a socket operation —
  -- which closing does — would wait for itself; so the close is handed to a task of its
  -- own, which exists only for a connection that actually timed out.
  let _ ← IO.mapTask (t := fired.result?) fun r => do
    if r.isSome then
      let _ ← IO.asTask (prio := .dedicated) s.close
  try go already 4096 finally timer.stop
where
  go (buf : Bytes) (fuel : Nat) : IO (Option (Http.Request × Bytes)) := do
    match Http.readRequest buf limits with
    | .done r consumed => return some (r, Bytes.drop buf consumed)
    | .error e => throw (IO.userError e)
    | .need =>
      match fuel with
      | 0 => throw (IO.userError "the request head never ended")
      | fuel + 1 => do
        let chunk ← s.read 65536
        if chunk.size == 0 then
          -- A clean end between requests is how a connection normally closes;
          -- a partial head is not.
          if buf.size == 0 then return none
          else throw (IO.userError "the client closed mid-request")
        go (buf ++ chunk) fuel

/-- Undo rewrite mode's path encoding: `/<scheme>/<host>/<rest>`. -/
def unrewrite? (target : String) : Option (String × String × String) := do
  let segments := (Str.pathOnly target).splitOn "/" |>.filter (!·.isEmpty)
  match segments with
  | scheme :: host :: rest =>
    if scheme != "http" && scheme != "https" then none
    else
      let query := match Str.splitOnce? target "?" with
        | some (_, q) => "?" ++ q
        | none => ""
      some (scheme, host, "/" ++ "/".intercalate rest ++ query)
  | _ => none

/-- Handle the requests arriving on one already-identified stream. -/
partial def serveRequests (ctx : Context) (client : Net.Stream) (token : Biscuit)
    (scheme : String) (tunnel : Option (String × Nat)) (clientIp : String)
    (pending : Bytes) (served : Nat := 0) : IO Unit := do
  let limits : Http.Limits := { maxHeadSize := ctx.config.maxHeadSize }
  match ← readHead client limits pending with
  | none => return ()
  | some (wire, rest) =>
    let last := served + 1 ≥ ctx.config.maxRequestsPerConnection
    let more ← forward ctx { client, wire, pipelined := rest, scheme, tunnel, token, clientIp
                             closeAfter := last }
    -- Every request on the connection is decided on its own, so carrying many
    -- costs nothing in authority; the bound is there so one client cannot hold
    -- a connection, and the TLS session under it, forever.
    if more && served + 1 < ctx.config.maxRequestsPerConnection then
      serveRequests ctx client token scheme tunnel clientIp ByteArray.empty (served + 1)

/-- Peek at the ClientHello to find the name the client asked for.

The bytes are kept and handed to the session afterwards, so the peek costs
nothing: they were going to be buffered anyway. -/
def peekSni (raw : Net.Stream) (already : Bytes := ByteArray.empty) :
    IO (Bytes × Option String) := do
  let rec go (buf : Bytes) (fuel : Nat) : IO (Bytes × Option String) := do
    match Net.clientHelloSni? buf with
    | some sni => return (buf, some sni)
    | none =>
      if buf.size > 5 && buf.size ≥ Net.clientHelloNeeded buf then return (buf, none)
      match fuel with
      | 0 => return (buf, none)
      | fuel + 1 => do
        let chunk ← raw.read 8192
        if chunk.size == 0 then return (buf, none)
        go (buf ++ chunk) fuel
  go already 64

/-- Copy one direction of a tunnel until its source ends. -/
partial def pump (src dst : Net.Stream) : IO Unit := do
  let chunk ← src.read 65536
  if chunk.size == 0 then return
  dst.write chunk
  pump src dst

/-- A blind tunnel to a host no manifest claims, for the configuration's
`passthrough`.  Nothing is intercepted and nothing is spent: the bytes are the
client's TLS session with the origin, which this proxy cannot read and does not
try to.  What it does check is the token — revoked or expired, and the tunnel
is refused — and it writes one audit record per tunnel. -/
def tunnelBlind (ctx : Context) (client : Net.Stream) (host : String) (port : Nat)
    (token : Biscuit) (clientIp : String) (already : Bytes := ByteArray.empty) : IO Unit := do
  let requestId ← ctx.nextRequestId
  if let .error e ← tokenHolds ctx token then
    refuse client 407 requestId s!"the token was not accepted: {e}"
    return
  let record : AuditRecord := {
    time := ← Store.now, requestId, method := "CONNECT", url := s!"{host}:{port}"
    clientIp, service := "passthrough", manifestVersion := "", grant := ""
    grantVersion := ""
    revocationIds := (Biscuit.revocationIdentifiers token).map Bytes.toHex
    allowed := true, outcome := "passthrough", facts := []
    credential := none, status := none }
  if !ctx.config.passesPort port then
    refuse client 403 requestId s!"passthrough is not allowed to port {port}"
    return
  let origin ← try
      Net.Tcp.connectChecked host (UInt16.ofNat port)
        fun a => ctx.config.passthroughInternal || !Net.Tcp.isInternal a
    catch e => do
      refuse client 502 requestId s!"the origin could not be reached: {e}"
      if ctx.config.audit then
        ctx.audit.append { record with outcome := s!"passthrough, upstream failure: {e}" }
      return
  if ctx.config.audit then ctx.audit.append record
  client.write (Bytes.ofString "HTTP/1.1 200 Connection established\r\n\r\n")
  -- A client that sent its first bytes straight after the CONNECT, without waiting
  -- for the answer, has them relayed rather than lost.
  if already.size > 0 then origin.write already
  -- Whichever side ends first ends the tunnel.  The bytes are a TLS session
  -- the proxy cannot read, so it cannot tell a half-close from a finished
  -- exchange; and an origin left waiting after its client went away holds a
  -- connection open for as long as it cares to, which for a keep-alive server
  -- is indefinitely.  `Stream.close` also stops reads on that stream, so
  -- closing one side unblocks the copy reading from it.
  let _ ← IO.asTask (prio := .dedicated) do
    try pump client origin catch _ => pure ()
    origin.close
  try pump origin client catch _ => pure ()
  origin.close

/-- Handle a `CONNECT`: intercept, then serve what comes through. -/
def handleConnect (ctx : Context) (client : Net.Stream) (wire : Http.Request)
    (token : Biscuit) (clientIp : String) (already : Bytes := ByteArray.empty) : IO Unit := do
  let (host, port) := match Str.splitOnce? wire.target ":" with
    | some (h, p) => (Str.toLowerAscii h, p.toNat?.getD 443)
    | none => (Str.toLowerAscii wire.target, 443)
  let registry ← ctx.registry.get
  match registry.forHost? host with
  | none =>
    -- Refused rather than tunnelled, unless the configuration names the host:
    -- this is a credential proxy, not an anonymous egress path, and a tunnel it
    -- cannot inspect is one it cannot gate.
    if ctx.config.passes host then tunnelBlind ctx client host port token clientIp already
    else do
      let requestId ← ctx.nextRequestId
      refuse client 403 requestId s!"no service manifest claims `{host}`"
  | some _ => do
    client.write (Bytes.ofString "HTTP/1.1 200 Connection established\r\n\r\n")
    let (hello, sni) ← peekSni client already
    let name := sni.getD host
    let serverCtx ← ctx.ca.contextFor name
    let tls ← Net.tlsServer serverCtx client hello
    try
      serveRequests ctx tls token "https" (some (host, port)) clientIp ByteArray.empty
    catch _ => pure ()
    tls.close

/-- Is this absolute-form request addressed to the proxy itself?

It happens when both interception modes are configured at once: `insteadOf`
rewrites the URL to point at the proxy, and `http.proxy` then sends that
rewritten URL *through* the proxy, so the daemon is asked to fetch from itself.
The symptom is a refusal naming the proxy's own address as an unknown service,
which takes a while to recognise for what it is. -/
def addressedToSelf? (ctx : Context) (target : String) : Option String :=
  let rest :=
    if target.startsWith "http://" then some (Str.stripPrefix target "http://")
    else if target.startsWith "https://" then some (Str.stripPrefix target "https://")
    else none
  rest.bind fun r =>
    let authority := (r.splitOn "/").headD r
    let (host, port) := match Str.splitOnce? authority ":" with
      | some (h, p) => (h, p.toNat?.getD 80)
      | none => (authority, 80)
    if host == ctx.config.listenHost && port == ctx.config.listenPort.toNat then
      let path := Str.stripPrefix r authority
      some (if (unrewrite? path).isSome then
        "both interception modes are configured: `insteadOf` rewrote the URL to \
        point at this proxy, and `http.proxy` then sent it through this proxy. \
        Unset one — run `kleis setup --mode rewrite` or `kleis setup --mode connect`, \
        which unsets the other for you"
      else
        "this request is addressed to the proxy itself; check `http.proxy` and \
        any `insteadOf` rewrites")
    else none

/-- Handle a rewrite-mode request, whose target carries the origin. -/
def handleRewrite (ctx : Context) (client : Net.Stream) (wire : Http.Request)
    (rest : Bytes) (token : Biscuit) (clientIp requestId : String) : IO Unit := do
  match unrewrite? wire.target with
  | none =>
    refuse client 400 requestId "in rewrite mode a target is `/<scheme>/<host>/<path>`"
  | some (scheme, host, target) =>
    let headers := Http.Headers.set wire.headers "host" host
    let port := if scheme == "https" then 443 else 80
    let _ ← forward ctx {
      client, wire := { wire with target, headers }
      pipelined := rest, scheme, tunnel := some (host, port), token, clientIp, closeAfter := true }
    pure ()

/-- Handle one client connection from the moment it is accepted. -/
def handleConnection (ctx : Context) (client : Net.Stream) (clientIp : String) : IO Unit := do
  let limits : Http.Limits := { maxHeadSize := ctx.config.maxHeadSize }
  match ← readHead client limits ByteArray.empty with
  | none => return ()
  | some (wire, rest) =>
    let requestId ← ctx.nextRequestId
    match bearerFrom? wire.headers with
    | none =>
      -- Both schemes are offered.  `Bearer` is what a person would write by
      -- hand; `Basic` is what git and curl actually negotiate, because their
      -- default `anyauth` probe sends no credential, reads the challenge, and
      -- retries with a scheme it recognises — and it does not recognise
      -- `Bearer` for a proxy.  Offering only `Bearer` makes `http.proxy` fail
      -- with no useful message.
      client.write (Http.simpleResponse 407 "text/plain; charset=utf-8"
        "kleis: present a biscuit in Proxy-Authorization\n"
        #[("proxy-authenticate", "Basic realm=\"kleis\""),
          ("proxy-authenticate", "Bearer realm=\"kleis\""),
          ("x-kleis-request-id", requestId)])
    | some text =>
      match Token.parse text ctx.rootPublic with
      | .error e => refuse client 407 requestId s!"the token was not accepted: {e}"
      | .ok token =>
        if isAdminTarget wire.target then
          handleAdmin ctx client wire rest token clientIp
        else if wire.method == "CONNECT" then
          if ctx.config.mode.intercepts then handleConnect ctx client wire token clientIp rest
          else refuse client 405 requestId "this proxy is not configured to intercept CONNECT"
        else if wire.target.startsWith "http://" || wire.target.startsWith "https://" then
          match addressedToSelf? ctx wire.target with
          | some diagnosis => refuse client 400 requestId diagnosis
          | none =>
            let _ ← forward ctx { client, wire, pipelined := rest, scheme := "http"
                                  tunnel := none, token, clientIp, closeAfter := true }
            pure ()
        else if ctx.config.mode.rewrites then
          handleRewrite ctx client wire rest token clientIp requestId
        else refuse client 400 requestId "this proxy expects an absolute target or CONNECT"

end Proxy
end Kleis
