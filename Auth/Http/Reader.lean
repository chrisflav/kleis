import Auth.Http.Message

/-!
# Reading messages

An incremental parser: it is handed everything received so far and answers
either "not yet", "here is the head and it ended at byte `n`", or "this is not
a message I will forward".

The refusals are the interesting part.  A proxy that disagrees with the origin
server about where one request ends and the next begins is a request smuggling
vulnerability, so anything ambiguous is rejected rather than guessed at:
`Content-Length` together with `Transfer-Encoding`, two `Content-Length` fields
that disagree, a length that is not a plain decimal number, and obsolete line
folding, which a downstream parser may well interpret differently.
-/

namespace Auth
namespace Http

open LeanBiscuit (Bytes)

/-- The result of an incremental parse. -/
inductive Parsed (α : Type) where
  /-- Nothing conclusive yet; feed more bytes. -/
  | need
  /-- Parsed, having consumed this many bytes from the front. -/
  | done (value : α) (consumed : Nat)
  /-- Malformed, with a reason fit for a log line and a `400`. -/
  | error (message : String)
  deriving Repr

/-- Limits on a header block, so that a peer cannot make us buffer without
bound before we have any idea who they are. -/
structure Limits where
  /-- The largest header block, in bytes, including the request line. -/
  maxHeadSize : Nat := 65536
  /-- The largest number of header fields. -/
  maxHeaderCount : Nat := 200
  deriving Repr, Inhabited

/-- Split a header block into its lines, rejecting obsolete folding.

Lines are separated by CRLF; a bare LF is accepted because clients emit it and
every server tolerates it, but a line beginning with a space or a tab is an
`obs-fold` and is refused. -/
private def headLines (block : Bytes) : Except String (List String) :=
  let text := Bytes.toStringLossy block
  let raw := (text.splitOn "\r\n").flatMap (·.splitOn "\n")
  let lines := raw.filter (!·.isEmpty)
  if lines.any fun l => l.startsWith " " || l.startsWith "\t" then
    throw "obsolete line folding in the header block"
  else .ok lines

/-- Parse one `name: value` field. -/
private def parseField (line : String) : Except String (String × String) := do
  match Str.splitOnce? line ":" with
  | none => throw s!"malformed header field: {line}"
  | some (rawName, value) =>
    -- Checked *before* trimming.  RFC 9112 forbids whitespace between the
    -- field name and the colon, and a downstream parser that tolerated it
    -- would disagree with this one about where a field begins — which is the
    -- shape of a request smuggling bug.
    if rawName.any fun c => c == ' ' || c == '\t' then
      throw s!"whitespace in header field name: `{rawName}`"
    if rawName.isEmpty then throw "empty header field name"
    .ok (Str.toLowerAscii rawName, Str.trim value)

/-- Reject the framing ambiguities that make smuggling possible. -/
private def checkFraming (h : Headers) : Except String Unit := do
  let hasTe := Headers.contains h "transfer-encoding"
  let cls := Headers.findAll h "content-length"
  if hasTe && !cls.isEmpty then
    throw "both Content-Length and Transfer-Encoding are present"
  if hasTe then
    let te := Headers.tokens h "transfer-encoding"
    if te.back? != some "chunked" then
      throw "Transfer-Encoding does not end in chunked"
    if te.size > 1 then
      throw "a transfer coding other than chunked was requested"
  for v in cls do
    let v := Str.trim v
    if !Str.isDigits v then throw s!"malformed Content-Length: {v}"
  if cls.size > 1 then
    let distinct := cls.foldl (init := ([] : List String)) fun acc v =>
      let v := Str.trim v
      if acc.contains v then acc else v :: acc
    if distinct.length > 1 then throw "conflicting Content-Length fields"

/-- Locate the end of the header block: the first empty line. -/
private def findHeadEnd? (buf : Bytes) : Option (Nat × Nat) :=
  match Bytes.indexOf? buf (Bytes.ofString "\r\n\r\n") with
  | some i => some (i, i + 4)
  | none => match Bytes.indexOf? buf (Bytes.ofString "\n\n") with
    | some i => some (i, i + 2)
    | none => none

/-- Parse a request head. -/
def readRequest (buf : Bytes) (limits : Limits := {}) : Parsed Request :=
  match findHeadEnd? buf with
  | none =>
    if buf.size > limits.maxHeadSize then .error "header block too large" else .need
  | some (blockEnd, consumed) =>
    if consumed > limits.maxHeadSize then .error "header block too large" else
    match headLines (Bytes.take buf blockEnd) with
    | .error e => .error e
    | .ok [] => .error "empty request"
    | .ok (start :: fieldLines) =>
      if fieldLines.length > limits.maxHeaderCount then .error "too many header fields" else
      match start.splitOn " " with
      | method :: target :: rest =>
        let version := rest.headD "HTTP/1.1"
        if method.isEmpty || target.isEmpty then .error "malformed request line" else
        match fieldLines.mapM parseField with
        | .error e => .error e
        | .ok fields =>
          let headers : Headers := fields.toArray
          match checkFraming headers with
          | .error e => .error e
          | .ok _ =>
            .done { method := method.toUpper, target, version, headers,
                    framing := requestFraming headers } consumed
      | _ => .error "malformed request line"

/-- Parse a response head.  The request method is needed because it decides
whether a body is present at all. -/
def readResponse (buf : Bytes) (method : String) (limits : Limits := {}) : Parsed Response :=
  match findHeadEnd? buf with
  | none =>
    if buf.size > limits.maxHeadSize then .error "header block too large" else .need
  | some (blockEnd, consumed) =>
    if consumed > limits.maxHeadSize then .error "header block too large" else
    match headLines (Bytes.take buf blockEnd) with
    | .error e => .error e
    | .ok [] => .error "empty response"
    | .ok (start :: fieldLines) =>
      if fieldLines.length > limits.maxHeaderCount then .error "too many header fields" else
      match start.splitOn " " with
      | version :: code :: rest =>
        match code.toNat? with
        | none => .error s!"malformed status code: {code}"
        | some status =>
          match fieldLines.mapM parseField with
          | .error e => .error e
          | .ok fields =>
            let headers : Headers := fields.toArray
            match checkFraming headers with
            | .error e => .error e
            | .ok _ =>
              .done { version, status, reason := " ".intercalate rest, headers,
                      framing := responseFraming headers status method } consumed
      | _ => .error "malformed status line"

end Http
end Auth
