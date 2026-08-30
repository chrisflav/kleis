import Kleis.Util.Bytes
import Kleis.Util.Str

/-!
# HTTP messages

The wire-level view: a request line or a status line, a header block, and a
body whose framing is decided by the headers.  This is what comes off the
socket and what goes back onto it, and it stays as close to the bytes as it can
so that a request the proxy forwards is the request the client sent.

The normalized view the policy layer reasons about is `Kleis.Model.Request`;
this module deliberately knows nothing about it.
-/

namespace Kleis
namespace Http

open LeanBiscuit (Bytes)

/-- Header fields, in the order they were sent.

A list rather than a map: order is observable (`Set-Cookie` most obviously),
duplicates are legal and meaningful, and the proxy's job is to relay what it
was given.  Names are stored lowercased so that lookup is a comparison. -/
abbrev Headers := Array (String × String)

namespace Headers

/-- The first value for a name, which is what a well-formed message has at most
one of. -/
def find? (h : Headers) (name : String) : Option String :=
  let n := Str.toLowerAscii name
  (Array.find? (fun (k, _) => k == n) h).map (·.2)

/-- Every value for a name. -/
def findAll (h : Headers) (name : String) : Array String :=
  let n := Str.toLowerAscii name
  (Array.filter (fun (k, _) => k == n) h).map (·.2)

/-- Is the name present? -/
def contains (h : Headers) (name : String) : Bool := (find? h name).isSome

/-- Remove every field with this name. -/
def remove (h : Headers) (name : String) : Headers :=
  let n := Str.toLowerAscii name
  Array.filter (fun (k, _) => k != n) h

/-- Remove every field named in the list. -/
def removeAll (h : Headers) (names : List String) : Headers :=
  names.foldl (init := h) fun acc n => remove acc n

/-- Append a field, keeping any existing ones. -/
def add (h : Headers) (name value : String) : Headers :=
  h.push (Str.toLowerAscii name, value)

/-- Replace every field of this name with a single one. -/
def set (h : Headers) (name value : String) : Headers :=
  (remove h name).push (Str.toLowerAscii name, value)

/-- The comma-separated items of every field with this name, trimmed and
lowercased.  Used for `Connection`, `Transfer-Encoding` and friends, all of
which are `#rule` lists that may be split across fields. -/
def tokens (h : Headers) (name : String) : Array String :=
  (findAll h name).flatMap fun v =>
    ((v.splitOn ",").map fun t => Str.toLowerAscii (Str.trim t)).toArray.filter (!·.isEmpty)

end Headers

/-- How the end of a body is recognised. -/
inductive Framing where
  /-- No body at all. -/
  | empty
  /-- Exactly this many bytes. -/
  | length (n : Nat)
  /-- Chunked transfer coding. -/
  | chunked
  /-- Until the connection closes.  Only legal for a response. -/
  | untilClose
  deriving Repr, DecidableEq, Inhabited

/-- A request as it arrived, with the body still on the socket. -/
structure Request where
  /-- The method, uppercased. -/
  method : String
  /-- The request target exactly as sent. -/
  target : String
  /-- The HTTP version token, e.g. `HTTP/1.1`. -/
  version : String
  /-- The header block. -/
  headers : Headers
  /-- How the body is framed. -/
  framing : Framing
  deriving Repr, Inhabited

/-- A response as it arrived. -/
structure Response where
  /-- The HTTP version token. -/
  version : String
  /-- The status code. -/
  status : Nat
  /-- The reason phrase, which may be empty under HTTP/2 semantics. -/
  reason : String
  /-- The header block. -/
  headers : Headers
  /-- How the body is framed. -/
  framing : Framing
  deriving Repr, Inhabited

/-- Decide a request's framing from its headers.

`Transfer-Encoding` wins over `Content-Length` (RFC 9112 §6.3), and a message
carrying both is a request smuggling attempt rather than an ambiguity to
resolve — the reader rejects it before this is called. -/
def requestFraming (h : Headers) : Framing :=
  if (Headers.tokens h "transfer-encoding").contains "chunked" then .chunked
  else match Headers.find? h "content-length" >>= (·.trimAscii.toString.toNat?) with
    | some n => if n == 0 then .empty else .length n
    | none => .empty

/-- Decide a response's framing.  A status that is defined to have no body
never has one, whatever the headers say. -/
def responseFraming (h : Headers) (status : Nat) (method : String) : Framing :=
  if status == 204 || status == 304 || (100 ≤ status && status < 200) then .empty
  else if method == "HEAD" then .empty
  else if method == "CONNECT" && 200 ≤ status && status < 300 then .empty
  else if (Headers.tokens h "transfer-encoding").contains "chunked" then .chunked
  else match Headers.find? h "content-length" >>= (·.trimAscii.toString.toNat?) with
    | some n => if n == 0 then .empty else .length n
    | none => .untilClose

/-- Header fields that belong to one hop and must never be relayed to the next
(RFC 9110 §7.6.1), plus the proxy's own credential-bearing field. -/
def hopByHop : List String :=
  ["connection", "keep-alive", "proxy-authenticate", "proxy-authorization",
   "proxy-connection", "te", "trailer", "transfer-encoding", "upgrade"]

/-- Strip the hop-by-hop fields, including any the `Connection` field names.

The `Connection` list is honoured because that is how a hop declares a field
private to it; forwarding such a field would leak a header the sender expected
to be consumed here. -/
def stripHopByHop (h : Headers) : Headers :=
  let named := (Headers.tokens h "connection").toList
  Headers.removeAll h (hopByHop ++ named)

end Http
end Kleis
