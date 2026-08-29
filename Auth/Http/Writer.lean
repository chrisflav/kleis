import Auth.Http.Message

/-!
# Writing messages

Serialisation is the easy direction, with one rule worth stating: the proxy
writes the header fields it holds, in the order it holds them, and adds nothing
of its own beyond what framing requires.  A field the client sent and policy
allowed is a field the origin sees, spelled the same way.
-/

namespace Auth
namespace Http

open LeanBiscuit (Bytes)

/-- Render a header block, terminated by the empty line. -/
def writeHeaders (h : Headers) : Bytes :=
  Bytes.ofString (String.join (h.toList.map fun (k, v) => s!"{k}: {v}\r\n") ++ "\r\n")

/-- Render a request head. -/
def writeRequest (r : Request) : Bytes :=
  Bytes.ofString s!"{r.method} {r.target} {r.version}\r\n" ++ writeHeaders r.headers

/-- Render a response head. -/
def writeResponse (r : Response) : Bytes :=
  let line :=
    if r.reason.isEmpty then s!"{r.version} {r.status}\r\n"
    else s!"{r.version} {r.status} {r.reason}\r\n"
  Bytes.ofString line ++ writeHeaders r.headers

/-- The conventional reason phrase for a status the proxy generates itself. -/
def reasonFor (status : Nat) : String :=
  match status with
  | 200 => "OK"
  | 400 => "Bad Request"
  | 403 => "Forbidden"
  | 405 => "Method Not Allowed"
  | 407 => "Proxy Authentication Required"
  | 413 => "Content Too Large"
  | 421 => "Misdirected Request"
  | 500 => "Internal Server Error"
  | 502 => "Bad Gateway"
  | 504 => "Gateway Timeout"
  | _ => "Unknown"

/-- A complete response the proxy generates, with the body already in hand.

`Connection: close` is set unconditionally: every message this builds is a
refusal or an error, and keeping such a connection alive invites the client to
pipeline more requests behind a decision it has not yet read. -/
def simpleResponse (status : Nat) (contentType body : String)
    (extra : Headers := #[]) : Bytes :=
  let payload := Bytes.ofString body
  let headers : Headers :=
    #[("content-type", contentType),
      ("content-length", toString payload.size),
      ("connection", "close")] ++ extra
  writeResponse { version := "HTTP/1.1", status, reason := reasonFor status,
                  headers, framing := .length payload.size } ++ payload

end Http
end Auth
