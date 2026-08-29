import Auth.Proxy.Forward
import Auth.Net.ClientHello
import Auth.Net.TlsStream
import Auth.Net.Socket

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
`X-Auth-Token` exists for `http.extraHeader`.

On a `CONNECT` the header is on the tunnel request, and the requests inside it
have none — so the token is captured once and carried.  Whatever the client
sends inside is stripped, so a bearer cannot upgrade themselves mid-tunnel.
-/

namespace Auth
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
    match Http.Headers.find? headers "x-auth-token" with
    | some v => some (Str.trim v)
    | none => (Http.Headers.find? headers "authorization").bind fromAuth

/-- Read one request head from a stream, returning it and whatever was read
past it. -/
def readHead (s : Net.Stream) (limits : Http.Limits) (already : Bytes) :
    IO (Option (Http.Request × Bytes)) := do
  let rec go (buf : Bytes) (fuel : Nat) : IO (Option (Http.Request × Bytes)) := do
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
  go already 4096

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
    (pending : Bytes) : IO Unit := do
  let limits : Http.Limits := { maxHeadSize := ctx.config.maxHeadSize }
  match ← readHead client limits pending with
  | none => return ()
  | some (wire, rest) =>
    let more ← forward ctx { client, wire, pipelined := rest, scheme, tunnel, token, clientIp }
    if more then serveRequests ctx client token scheme tunnel clientIp ByteArray.empty

/-- Peek at the ClientHello to find the name the client asked for.

The bytes are kept and handed to the session afterwards, so the peek costs
nothing: they were going to be buffered anyway. -/
def peekSni (raw : Net.Stream) : IO (Bytes × Option String) := do
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
  go ByteArray.empty 64

/-- Handle a `CONNECT`: intercept, then serve what comes through. -/
def handleConnect (ctx : Context) (client : Net.Stream) (wire : Http.Request)
    (token : Biscuit) (clientIp : String) : IO Unit := do
  let (host, port) := match Str.splitOnce? wire.target ":" with
    | some (h, p) => (Str.toLowerAscii h, p.toNat?.getD 443)
    | none => (Str.toLowerAscii wire.target, 443)
  let registry ← ctx.registry.get
  match registry.forHost? host with
  | none => do
    -- Refused rather than tunnelled: this is a credential proxy, not an
    -- anonymous egress path, and a tunnel it cannot inspect is one it cannot
    -- gate.
    let requestId ← ctx.nextRequestId
    refuse client 403 requestId s!"no service manifest claims `{host}`"
  | some _ => do
    client.write (Bytes.ofString "HTTP/1.1 200 Connection established\r\n\r\n")
    let (hello, sni) ← peekSni client
    let name := sni.getD host
    let serverCtx ← ctx.ca.contextFor name
    let tls ← Net.tlsServer serverCtx client hello
    try
      serveRequests ctx tls token "https" (some (host, port)) clientIp ByteArray.empty
    catch _ => pure ()
    tls.close

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
      pipelined := rest, scheme, tunnel := some (host, port), token, clientIp }
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
        "auth: present a biscuit in Proxy-Authorization\n"
        #[("proxy-authenticate", "Basic realm=\"auth\""),
          ("proxy-authenticate", "Bearer realm=\"auth\""),
          ("x-auth-request-id", requestId)])
    | some text =>
      match Token.parse text ctx.rootPublic with
      | .error e => refuse client 407 requestId s!"the token was not accepted: {e}"
      | .ok token =>
        if wire.method == "CONNECT" then
          if ctx.config.mode.intercepts then handleConnect ctx client wire token clientIp
          else refuse client 405 requestId "this proxy is not configured to intercept CONNECT"
        else if wire.target.startsWith "http://" || wire.target.startsWith "https://" then
          let _ ← forward ctx { client, wire, pipelined := rest, scheme := "http"
                                tunnel := none, token, clientIp }
          pure ()
        else if ctx.config.mode.rewrites then
          handleRewrite ctx client wire rest token clientIp requestId
        else refuse client 400 requestId "this proxy expects an absolute target or CONNECT"

end Proxy
end Auth
