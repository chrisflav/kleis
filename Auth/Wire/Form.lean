import Auth.Wire.Decoder

/-!
# Form decoders

`application/x-www-form-urlencoded` is a query string in a body, and decodes to
a map.  A repeated name becomes an array, because dropping one of the values
would let a request smuggle a parameter past a policy that checked the other.

`multipart/form-data` is decoded to its part *headers* only: a multipart body
is a file upload, its parts are exactly the thing that must not be buffered,
and the name and content type of each part is what a policy can usefully say
something about.
-/

namespace Auth
namespace Wire

open LeanBiscuit (Bytes)
open LeanBiscuit.Datalog (Value ValueKey)

/-- Group repeated names, keeping order.  A name seen once maps to its value; a
name seen more than once maps to the array of its values. -/
private def groupPairs (pairs : List (String × String)) : Value :=
  let names := pairs.foldl (init := ([] : List String)) fun acc (k, _) =>
    if acc.contains k then acc else acc ++ [k]
  .map (names.map fun n =>
    let vs := (pairs.filter fun (k, _) => k == n).map (·.2)
    (ValueKey.str n, match vs with
      | [v] => Value.str v
      | _ => Value.array (vs.map Value.str)))

/-- Decode `application/x-www-form-urlencoded`. -/
def formDecoder : PureDecoder where
  name := "form"
  media := #["application/x-www-form-urlencoded"]
  step := fun buf complete =>
    if !complete then .need (buf.size + 1)
    else
      let text := Bytes.toStringLossy buf
      let pairs := (text.splitOn "&").filterMap fun part =>
        if part.isEmpty then none
        else match Str.splitOnce? part "=" with
          | some (k, v) => some (Str.percentDecode k true, Str.percentDecode v true)
          | none => some (Str.percentDecode part true, "")
      .done (groupPairs pairs) buf.size

/-- One parameter of a `Content-Disposition` field. -/
private def dispositionParam (field : String) (name : String) : Option String :=
  let parts := (field.splitOn ";").map Str.trim
  parts.findSome? fun p =>
    match Str.splitOnce? p "=" with
    | some (k, v) =>
      if Str.toLowerAscii (Str.trim k) == name then
        some (Str.stripSuffix (Str.stripPrefix (Str.trim v) "\"") "\"")
      else none
    | none => none

/-- Describe one part from its header block. -/
private def partSummary (headBlock : String) : Value :=
  let lines := ((headBlock.splitOn "\r\n").flatMap (·.splitOn "\n")).filter (!·.isEmpty)
  let fieldOf (n : String) : Option String :=
    lines.findSome? fun l =>
      match Str.splitOnce? l ":" with
      | some (k, v) => if Str.toLowerAscii (Str.trim k) == n then some (Str.trim v) else none
      | none => none
  let disp := (fieldOf "content-disposition").getD ""
  .map [
    (.str "name", match dispositionParam disp "name" with
      | some n => .str n | none => .null),
    (.str "filename", match dispositionParam disp "filename" with
      | some n => .str n | none => .null),
    (.str "content_type", match fieldOf "content-type" with
      | some t => .str t | none => .null)]

/-- Walk the parts of a multipart body, collecting their headers. -/
private def multipartParts (buf : Bytes) (sep : Bytes) : Nat → Nat → List Value → List Value
  | _, 0, acc => acc.reverse
  | i, fuel + 1, acc =>
    match Bytes.indexOf? buf sep i with
    | none => acc.reverse
    | some j =>
      let afterSep := j + sep.size
      match Bytes.indexOf? buf (Bytes.ofString "\r\n\r\n") afterSep with
      | none => acc.reverse
      | some headEnd =>
        let head := Bytes.toStringLossy (Bytes.slice buf afterSep headEnd)
        multipartParts buf sep (headEnd + 4) fuel (partSummary head :: acc)

/-- Decode the part headers of a `multipart/form-data` body.

The boundary is not available here — it lives in the `Content-Type` field — so
it is discovered from the body itself: the first line of a multipart body is
the delimiter by construction. -/
def multipartDecoder : PureDecoder where
  name := "multipart"
  media := #["multipart/form-data", "multipart/mixed", "multipart/related"]
  step := fun buf _ =>
    match Bytes.indexOf? buf (Bytes.ofString "\r\n") with
    | none => .need (buf.size + 1)
    | some j =>
      let sep := Bytes.take buf j
      if sep.size < 3 then .opaque
      else
        let parts := multipartParts buf sep 0 256 []
        .done (.map [(.str "parts", .array parts),
                     (.str "part_count", .integer parts.length)]) buf.size

end Wire
end Auth
