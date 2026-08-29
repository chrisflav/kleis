import AuthTests.Harness

/-! # HTTP framing

The refusals matter more than the acceptances: a proxy that disagrees with the
origin about where one request ends is a request smuggling vulnerability, so
the ambiguous cases are tested for being rejected. -/

namespace AuthTests

open Auth LeanBiscuit

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
    checkEq "decoded" (Auth.Bytes.toStringLossy entity) "hello world"
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

  group "http writing"
  let out := Http.simpleResponse 403 "text/plain" "no\n"
  let text := Auth.Bytes.toStringLossy out
  check "status line" (text.startsWith "HTTP/1.1 403 Forbidden")
  check "content length" ((text.splitOn "content-length: 3").length == 2)
  check "closes the connection" ((text.splitOn "connection: close").length == 2)

end AuthTests
