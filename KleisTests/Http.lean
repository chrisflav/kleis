import KleisTests.Harness

/-! # HTTP framing

The refusals matter more than the acceptances: a proxy that disagrees with the
origin about where one request ends is a request smuggling vulnerability, so
the ambiguous cases are tested for being rejected. -/

namespace KleisTests

open Kleis LeanBiscuit

private def req (s : String) : Http.Parsed Http.Request := Http.readRequest (Bytes.ofString s)

private def isError : Http.Parsed α → Bool
  | .error _ => true
  | _ => false

private def isNeed : Http.Parsed α → Bool
  | .need => true
  | _ => false

def httpTests : IO Unit := do
  group "http reading"
  match req "GET /a?b=1 HTTP/1.1\r\nHost: x.com\r\n\r\n" with
  | .done r consumed => do
    checkEq "method" r.method "GET"
    checkEq "target" r.target "/a?b=1"
    checkEq "host header" (Http.Headers.find? r.headers "host") (some "x.com")
    checkEq "consumed the head" consumed 36
    check "no body" (r.framing == Http.Framing.empty)
  | _ => check "a simple request parses" false

  check "a partial head asks for more" (isNeed (req "GET / HTTP/1.1\r\nHost: x"))

  match req "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello" with
  | .done r _ => check "content length framing" (r.framing == Http.Framing.length 5)
  | _ => check "a request with a body parses" false

  check "Content-Length with Transfer-Encoding is refused"
    (isError (req "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n"))
  check "conflicting Content-Length is refused"
    (isError (req "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\n"))
  check "a non-numeric Content-Length is refused"
    (isError (req "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5x\r\n\r\n"))
  check "obsolete line folding is refused"
    (isError (req "GET / HTTP/1.1\r\nHost: x\r\n  continued\r\n\r\n"))
  check "whitespace before the colon is refused"
    (isError (req "GET / HTTP/1.1\r\nHost : x\r\n\r\n"))
  check "a transfer coding other than chunked is refused"
    (isError (req "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: gzip, chunked\r\n\r\n"))

  group "hop-by-hop"
  let headers : Http.Headers :=
    #[("connection", "x-private"), ("x-private", "secret"), ("keep-alive", "5"),
      ("accept", "*/*")]
  let stripped := Http.stripHopByHop headers
  check "Connection itself goes" (!Http.Headers.contains stripped "connection")
  check "a field Connection names goes" (!Http.Headers.contains stripped "x-private")
  check "Keep-Alive goes" (!Http.Headers.contains stripped "keep-alive")
  check "everything else stays" (Http.Headers.contains stripped "accept")

  group "chunked"
  let body := Bytes.ofString "5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n"
  match Http.Chunked.decode body 1000 with
  | .done entity _ complete => do
    checkEq "decoded" (Kleis.Bytes.toStringLossy entity) "hello world"
    check "complete" complete
  | _ => check "a chunked body decodes" false
  match Http.Chunked.scan body with
  | .done n => checkEq "scan finds the end" n body.size
  | _ => check "a chunked body scans" false
  match Http.Chunked.scan (Bytes.ofString "5\r\nhel") with
  | .need => check "a partial chunked body asks for more" true
  | _ => check "a partial chunked body asks for more" false
  -- The prefix case the proxy depends on: stop early, do not buffer the rest.
  match Http.Chunked.decode body 3 with
  | .done entity _ complete => do
    check "stops at the limit" (entity.size ≥ 3 && entity.size < 11)
    check "and says it is not complete" (!complete)
  | _ => check "a chunked body decodes to a limit" false

  group "chunked, read as it arrives"
  -- Fed in pieces of every size, the reader agrees with `decode` and `scan`.
  let feedAll (r : Http.Chunked.Reader) (data : Bytes) (piece : Nat) :
      Except String (Http.Chunked.Reader × Option Nat) := do
    let mut r := r
    let mut i := 0
    for _ in [0:data.size + 1] do
      if i ≥ data.size then break
      let chunk := Kleis.Bytes.slice data i (i + piece)
      let (r', ended) ← r.feed chunk
      r := r'
      if let some k := ended then return (r, some (i + k))
      i := i + chunk.size
    return (r, none)
  let trailing := body ++ Bytes.ofString "GET / HTTP/1.1\r\n"
  for piece in [1, 2, 3, 7, 1000] do
    match feedAll { limit := 1000 } trailing piece with
    | .ok (r, some n) =>
      checkEq s!"pieces of {piece}: the entity" (Kleis.Bytes.toStringLossy r.entity) "hello world"
      checkEq s!"pieces of {piece}: where the body ends" n body.size
      check s!"pieces of {piece}: nothing let go" (!r.overflow)
    | _ => check s!"pieces of {piece}: the body is read to its end" false
  match feedAll { limit := 3 } body 1 with
  | .ok (r, some _) =>
    checkEq "past the limit the data is let go" r.entity.size 3
    check "and it says so" r.overflow
  | _ => check "a body past the limit is still read to its end" false
  match feedAll {} (Bytes.ofString "5\r\nhel") 1 with
  | .ok (_, none) => check "a partial body asks for more" true
  | _ => check "a partial body asks for more" false
  check "a size line that is not hex is refused"
    (({} : Http.Chunked.Reader).feed (Bytes.ofString "zz\r\n")).toOption.isNone
  check "so is one too long"
    (({} : Http.Chunked.Reader).feed (Bytes.ofString (String.ofList (List.replicate 9000 '0')))).toOption.isNone
  for (name, framed) in [
      ("a size line ending in a bare LF", "5\nhello\r\n0\r\n\r\n"),
      ("data followed by something other than CRLF", "5\r\nhelloXY0\r\n\r\n"),
      ("data followed by a bare LF", "5\r\nhello\n0\r\n\r\n"),
      ("a trailer line ending in a bare LF", "0\r\nx-a: 1\n\r\n"),
      ("a bare LF ending the trailers", "0\r\n\n")] do
    check s!"{name} is refused"
      ((feedAll {} (Bytes.ofString framed) 1).toOption.isNone
        && (match Http.Chunked.scan (Bytes.ofString framed) with | .error _ => true | _ => false))
  match feedAll {} (Bytes.ofString "0\r\nx-a: 1\r\nx-b: 2\r\n\r\n") 1 with
  | .ok (_, some n) => checkEq "trailers are read to the empty line" n 21
  | _ => check "trailers are read to the empty line" false

  group "http writing"
  let out := Http.simpleResponse 403 "text/plain" "no\n"
  let text := Kleis.Bytes.toStringLossy out
  check "status line" (text.startsWith "HTTP/1.1 403 Forbidden")
  check "content length" ((text.splitOn "content-length: 3").length == 2)
  check "closes the connection" ((text.splitOn "connection: close").length == 2)

end KleisTests
