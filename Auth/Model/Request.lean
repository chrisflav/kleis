import Auth.Http.Message
import Auth.Util.Json

/-!
# The normalized request

One type, from the interceptor down to the audit log.  Everything specific to
how the request arrived — which port it came in on, whether it was tunnelled
through a `CONNECT`, whether the target was absolute or origin-form — has been
resolved by the time a value of this type exists, so that no stage below the
interceptor has to know which interception mode is in use.

The body is a *prefix*.  A push is far larger than anything worth buffering, so
what is carried here is the leading bytes a decoder was given, together with
whether that is all of it.  A policy that needs more than the prefix has to say
so, and gets a refusal rather than an unbounded read.
-/

namespace Auth
namespace Model

open LeanBiscuit (Bytes)

/-- A request, normalized. -/
structure Request where
  /-- The method, uppercased. -/
  method : String
  /-- `http` or `https`. -/
  scheme : String
  /-- The origin host, lowercased, without the port. -/
  host : String
  /-- The origin port, defaulted from the scheme. -/
  port : Nat
  /-- The path, percent-decoded once, without the query. -/
  path : String
  /-- The path split on `/`, with empty segments dropped. -/
  segments : Array String
  /-- The decoded query parameters, in order. -/
  query : Array (String × String)
  /-- The request headers, names lowercased. -/
  headers : Http.Headers
  /-- The leading bytes of the entity body. -/
  bodyPrefix : Bytes
  /-- Whether `bodyPrefix` is the whole body. -/
  bodyComplete : Bool
  /-- The declared body length, when the framing gave one. -/
  bodySize : Option Nat
  deriving Inhabited

/-- The `host:port` authority, omitting a default port. -/
def Request.authority (r : Request) : String :=
  if (r.scheme == "https" && r.port == 443) || (r.scheme == "http" && r.port == 80)
  then r.host else s!"{r.host}:{r.port}"

/-- The request target to send upstream: origin-form, path and query. -/
def Request.originTarget (r : Request) : String :=
  let q :=
    if r.query.isEmpty then ""
    else "?" ++ "&".intercalate (r.query.toList.map fun (k, v) =>
      s!"{Str.percentEncode k}={Str.percentEncode v}")
  (if r.path.isEmpty then "/" else r.path) ++ q

/-- The absolute URL, for logs and for deciding redirects. -/
def Request.url (r : Request) : String :=
  s!"{r.scheme}://{r.authority}{r.originTarget}"

/-- Build a normalized request from a wire request and the authority the
connection established.

The target may be absolute (a proxied request), origin-form (a tunnelled one)
or authority-form; the `Host` field is the fallback and the tunnel's authority
is the last resort.  Where they disagree the *target* wins, because that is
what the client asked for and what the origin will route on. -/
def Request.ofWire (w : Http.Request) (scheme : String) (tunnel : Option (String × Nat))
    (bodyPrefix : Bytes) (bodyComplete : Bool) : Except String Request := do
  let (scheme, authority, target) ←
    if w.target.startsWith "http://" then
      let rest := Str.stripPrefix w.target "http://"
      match Str.splitOnce? rest "/" with
      | some (a, p) => pure ("http", a, "/" ++ p)
      | none => pure ("http", rest, "/")
    else if w.target.startsWith "https://" then
      let rest := Str.stripPrefix w.target "https://"
      match Str.splitOnce? rest "/" with
      | some (a, p) => pure ("https", a, "/" ++ p)
      | none => pure ("https", rest, "/")
    else
      let a ← match Http.Headers.find? w.headers "host", tunnel with
        | some h, _ => pure h
        | none, some (h, p) => pure s!"{h}:{p}"
        | none, none => throw "the request has no Host field and is not tunnelled"
      pure (scheme, a, w.target)
  let defaultPort := if scheme == "https" then 443 else 80
  let (host, port) := match Str.splitOnce? authority ":" with
    | some (h, p) => (h, p.toNat?.getD defaultPort)
    | none => (authority, defaultPort)
  let host := Str.toLowerAscii (Str.trim host)
  if host.isEmpty then throw "the request has an empty host"
  pure {
    method := w.method
    scheme
    host
    port
    path := Str.percentDecode (Str.pathOnly target)
    segments := Str.pathSegments target
    query := Str.parseQuery target
    headers := w.headers
    bodyPrefix
    bodyComplete
    bodySize := match w.framing with | .length n => some n | _ => none
  }

/-- A response, normalized, for the response-side facts. -/
structure Response where
  /-- The status code. -/
  status : Nat
  /-- The response headers. -/
  headers : Http.Headers
  /-- The leading bytes of the entity body. -/
  bodyPrefix : Bytes
  /-- Whether `bodyPrefix` is the whole body. -/
  bodyComplete : Bool
  deriving Inhabited

end Model
end Auth
