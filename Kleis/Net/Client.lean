import Kleis.Net.Socket
import Kleis.Net.TlsStream
import Kleis.Http.Reader
import Kleis.Http.Writer
import Kleis.Http.Chunked

/-!
# An HTTP client

For the daemon's own outbound calls — refreshing an OAuth token, minting a
GitHub App installation token — and for the proxy's connection to the origin.

It is built on the same reader and writer as the proxy, which is the point: a
framing bug shows up in both halves at once rather than lurking in whichever
one is tested less.

Redirects are *not* followed here.  The proxy re-authorizes each hop and
re-checks the credential's host binding, so following a redirect silently is
exactly the behaviour that must not exist in the layer underneath.
-/

namespace Kleis
namespace Net

open LeanBiscuit (Bytes)

/-- A response with its body in hand. -/
structure Fetched where
  /-- The status code. -/
  status : Nat
  /-- The header fields. -/
  headers : Http.Headers
  /-- The entity body. -/
  body : Bytes
  deriving Inhabited

/-- The body as text. -/
def Fetched.text (f : Fetched) : String := Bytes.toStringLossy f.body

/-- Read a complete response from a stream, buffering the body.

Only for the daemon's own calls, where the bodies are small JSON documents.
The proxy never uses this: it streams. -/
def readResponse (s : Stream) (method : String) (maxBody : Nat) : IO Fetched := do
  let rec readHead (buf : Bytes) (fuel : Nat) : IO (Http.Response × Bytes) := do
    match fuel with
    | 0 => throw (IO.userError "the response head never ended")
    | fuel + 1 =>
      match Http.readResponse buf method with
      | .done r consumed => pure (r, Bytes.drop buf consumed)
      | .error e => throw (IO.userError s!"malformed response: {e}")
      | .need => do
        let chunk ← s.read 65536
        if chunk.size == 0 then throw (IO.userError "the connection closed mid-response")
        readHead (buf ++ chunk) fuel
  let (response, rest) ← readHead ByteArray.empty 4096
  -- Read until the predicate says there is enough, or the peer stops.
  let drain (acc : Bytes) (enough : Bytes → Bool) : IO Bytes := do
    let rec go (acc : Bytes) (fuel : Nat) : IO Bytes := do
      if enough acc then return acc
      match fuel with
      | 0 => return acc
      | fuel + 1 => do
        let chunk ← s.read 65536
        if chunk.size == 0 then return acc
        go (acc ++ chunk) fuel
    go acc 100000
  let body ← match response.framing with
    | .empty => pure ByteArray.empty
    | .length n => do
      let full ← drain rest (fun b => b.size ≥ min n maxBody)
      pure (Bytes.take full (min n maxBody))
    | .chunked => do
      let full ← drain rest fun b =>
        match Http.Chunked.scan b with
        | .done _ => true
        | .error _ => true
        | .need => b.size ≥ maxBody
      match Http.Chunked.decode full maxBody with
      | .done body _ _ => pure body
      | .error e => throw (IO.userError s!"malformed chunked body: {e}")
      | .need => throw (IO.userError "the chunked body never ended")
    | .untilClose => drain rest (fun b => b.size ≥ maxBody)
  return { status := response.status, headers := response.headers, body }

/-- Open a connection to an origin, wrapping it in TLS when the scheme calls
for it. -/
def openOrigin (clientCtx : Tls.Context) (scheme host : String) (port : UInt16) : IO Stream := do
  let raw ← Tcp.connect host port
  if scheme == "https" then tlsClient clientCtx raw host else pure raw

/-- Make one request and read the response. -/
def fetch (clientCtx : Tls.Context) (method url : String)
    (headers : Http.Headers := #[]) (body : Bytes := ByteArray.empty)
    (maxBody : Nat := 1048576) : IO Fetched := do
  let (scheme, rest) :=
    if url.startsWith "https://" then ("https", Str.stripPrefix url "https://")
    else if url.startsWith "http://" then ("http", Str.stripPrefix url "http://")
    else ("https", url)
  let (authority, target) := match Str.splitOnce? rest "/" with
    | some (a, p) => (a, "/" ++ p)
    | none => (rest, "/")
  let (host, port) := match Str.splitOnce? authority ":" with
    | some (h, p) => (h, (p.toNat?.getD (if scheme == "https" then 443 else 80)))
    | none => (authority, if scheme == "https" then 443 else 80)
  let stream ← openOrigin clientCtx scheme host (UInt16.ofNat port)
  try
    let headers := headers
      |> (Http.Headers.set · "host" authority)
      |> (Http.Headers.set · "connection" "close")
      |> (fun h => if body.size == 0 then h
                   else Http.Headers.set h "content-length" (toString body.size))
    let head := Http.writeRequest
      { method := method.toUpper, target, version := "HTTP/1.1", headers
        framing := if body.size == 0 then .empty else .length body.size }
    stream.write (head ++ body)
    let response ← readResponse stream method.toUpper maxBody
    stream.close
    return response
  catch e =>
    stream.close
    throw e

end Net
end Kleis
