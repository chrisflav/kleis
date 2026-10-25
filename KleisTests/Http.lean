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

  group "chunked framing, strictly"
  for (name, framed) in [
      ("a trailer line of spaces", "5\r\n[1,2]\r\n0\r\n   \r\nGET"),
      ("a trailer line of a tab", "5\r\n[1,2]\r\n0\r\n\t\r\n"),
      ("a size of seventeen digits", "10000000000000005\r\n[1,2]\r\n0\r\n\r\n"),
      ("a bare CR in an extension", "5;a\rX\r\n[1,2]\r\n0\r\n\r\n"),
      ("spaces around the size", "  5  \r\n[1,2]\r\n0\r\n\r\n"),
      ("a space after the size", "5 \r\n[1,2]\r\n0\r\n\r\n"),
      ("a NUL after the size", "5\x00\r\n[1,2]\r\n0\r\n\r\n"),
      ("an empty extension", "5;\r\n[1,2]\r\n0\r\n\r\n"),
      ("a trailer with no colon", "5\r\n[1,2]\r\n0\r\nT\r\n\r\n"),
      ("a space before a trailer's colon", "5\r\n[1,2]\r\n0\r\nT : x\r\n\r\n"),
      ("a trailer line of a space, then the end", "5\r\n[1,2]\r\n0\r\n \r\n\r\n")] do
    check s!"{name} is refused"
      (match Http.Chunked.scan (Bytes.ofString framed) with | .error _ => true | _ => false)
  for (name, framed, consumed) in [
      ("sixteen digits", "0000000000000005\r\n[1,2]\r\n0\r\n\r\n", 30),
      ("a leading zero", "05\r\n[1,2]\r\n0\r\n\r\n", 16),
      ("an extension", "5;name=\"v\"\r\n[1,2]\r\n0\r\n\r\n", 24),
      ("a trailer field", "5\r\n[1,2]\r\n0\r\nx-a: 1\r\n\r\n", 23)] do
    checkEq s!"{name} is read" (match Http.Chunked.scan (Bytes.ofString framed) with
      | .done n => some n | _ => none) (some consumed)

  group "chunked framing, written again"
  -- What kleis sends upstream: its own size lines, no extension, no trailer.
  match feedAll {} (Bytes.ofString "5;ext=1\r\n[1,2]\r\n3\r\nabc\r\n0\r\nx-a: 1\r\n\r\n") 1000 with
  | .ok (r, some _) =>
    checkEq "in one read" (Kleis.Bytes.toStringLossy r.emitted) "5\r\n[1,2]\r\n3\r\nabc\r\n0\r\n\r\n"
  | _ => check "a chunked body is written again" false
  -- Read in pieces, a chunk split across reads is written as one chunk per piece.
  let mut written : Bytes := ByteArray.empty
  let mut reader : Http.Chunked.Reader := {}
  for piece in (Bytes.ofString "5;ext\r\nhello\r\n0\r\nx: y\r\n\r\n").toList.map (fun b => ByteArray.mk #[b]) do
    match reader.feed piece with
    | .ok (r, _) => reader := r; written := written ++ r.emitted
    | .error _ => pure ()
  checkEq "byte by byte"
    (Kleis.Bytes.toStringLossy written) "1\r\nh\r\n1\r\ne\r\n1\r\nl\r\n1\r\nl\r\n1\r\no\r\n0\r\n\r\n"
  check "and the result reads as the same entity"
    (match Http.Chunked.decode written 100 with
     | .done e _ true => Kleis.Bytes.toStringLossy e == "hello"
     | _ => false)

  group "where a head ends"
  let r2 := "GET /b HTTP/1.1\r\nHost: x\r\n\r\n"
  check "a bare-LF head is refused"
    (match Http.readRequest (Bytes.ofString ("GET /a HTTP/1.1\nHost: x\n\n" ++ r2)) with
     | .error _ => true | _ => false)
  check "so is one with a bare CR"
    (match Http.readRequest (Bytes.ofString "GET /a HTTP/1.1\r\nX: a\rb\r\n\r\n") with
     | .error _ => true | _ => false)
  check "and one whose last line ends in a bare LF"
    (match Http.readRequest (Bytes.ofString "GET /a HTTP/1.1\r\nHost: x\n\r\n") with
     | .error _ => true | _ => false)
  check "a bare-LF response head too"
    (match Http.readResponse (Bytes.ofString "HTTP/1.1 200 OK\ncontent-length: 0\n\n") "GET" with
     | .error _ => true | _ => false)

  group "http writing"
  let out := Http.simpleResponse 403 "text/plain" "no\n"
  let text := Kleis.Bytes.toStringLossy out
  check "status line" (text.startsWith "HTTP/1.1 403 Forbidden")
  check "content length" ((text.splitOn "content-length: 3").length == 2)
  check "closes the connection" ((text.splitOn "connection: close").length == 2)

end KleisTests
