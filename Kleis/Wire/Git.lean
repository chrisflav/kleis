import Kleis.Wire.Decoder

/-!
# The git decoders

Git's smart HTTP transport frames its requests as pkt-lines: four hexadecimal
digits giving the length of the line including those digits, then the payload.
`0000` ends a section, `0001` separates a version 2 command from its arguments.

This is the format the whole design turns on.  A `git push` is a `POST` whose
body is a handful of pkt-lines naming the refs being updated, followed by a
packfile of unbounded size.  The ref updates are at the *front*, so a decoder
that reads a few hundred bytes knows exactly which refs the push touches and
the packfile behind them never has to be buffered.

## What cannot be seen here

Whether a push is a *force* push is not on the wire.  The client sends the same
`<old> <new> <ref>` triple either way, and it is the receiving repository that
decides whether the update is a fast-forward by looking at its own object
graph — which a proxy does not have.  What can be decided from the bytes is
whether a ref is being **created** (the old id is zero) or **deleted** (the new
id is zero), and those are the facts emitted.  A policy that wants to forbid
history rewriting has to say so on the server, not here.
-/

namespace Kleis
namespace Wire

open LeanBiscuit (Bytes)
open LeanBiscuit.Datalog (Value ValueKey)

/-- One frame of the pkt-line encoding. -/
inductive Pkt where
  /-- A payload line, with the trailing line feed removed. -/
  | data (payload : String)
  /-- `0000`: the end of a section. -/
  | flush
  /-- `0001`: the separator between a version 2 command and its arguments. -/
  | delim
  /-- `0002`: the end of a response. -/
  | responseEnd
  deriving Repr, Inhabited

/-- How a pkt-line scan ended. -/
inductive PktScan where
  /-- Frames read, and the offset just past the last complete one. -/
  | frames (pkts : List Pkt) (offset : Nat) (sawFlush : Bool)
  /-- The bytes are not pkt-lines at all. -/
  | malformed
  deriving Inhabited

/-- Read pkt-lines until the buffer runs out or a section ends.

Reading stops at the first flush after at least one data line: for both
requests that matter the interesting content is the first section, and what
follows is a packfile or a negotiation that says nothing new about authority. -/
private def readPkts (buf : Bytes) : Nat → Nat → List Pkt → PktScan
  | i, 0, acc => .frames acc.reverse i false
  | i, fuel + 1, acc =>
    if i + 4 > buf.size then .frames acc.reverse i false
    else
      let header := Bytes.toStringLossy (Bytes.slice buf i (i + 4))
      match Str.ofHex? header with
      | none => if acc.isEmpty then .malformed else .frames acc.reverse i false
      | some 0 => .frames acc.reverse (i + 4) true
      | some 1 => readPkts buf (i + 4) fuel (.delim :: acc)
      | some 2 => readPkts buf (i + 4) fuel (.responseEnd :: acc)
      | some len =>
        if len < 4 then .malformed
        else if i + len > buf.size then .frames acc.reverse i false
        else
          let payload := Bytes.toStringLossy (Bytes.slice buf (i + 4) (i + len))
          let payload := Str.stripSuffix payload "\n"
          readPkts buf (i + len) fuel (.data payload :: acc)

/-- The data payloads of a frame list. -/
private def payloads (pkts : List Pkt) : List String :=
  pkts.filterMap fun p => match p with | .data s => some s | _ => none

/-- Is this object id all zeros?  Both SHA-1 and SHA-256 ids are handled, since
a repository may use either and the length is whatever the client sent. -/
private def isZeroOid (s : String) : Bool := !s.isEmpty && s.toList.all (· == '0')

/-- Split a first line into its content and the capability list that follows a
NUL byte.  Only the first line of a request carries capabilities. -/
private def splitCaps (s : String) : String × List String :=
  match Str.splitOnce? s (String.ofList [Char.ofNat 0]) with
  | some (content, caps) =>
    (content, (caps.splitOn " ").map Str.trim |>.filter (!·.isEmpty))
  | none => (s, [])

/-- Describe one ref update. -/
private def refUpdate (line : String) : Option Value :=
  match line.splitOn " " with
  | old :: new :: rest =>
    if rest.isEmpty then none else
      let ref := " ".intercalate rest
      some (.map [
        (.str "old", .str old),
        (.str "new", .str new),
        (.str "ref", .str ref),
        (.str "create", .bool (isZeroOid old)),
        (.str "delete", .bool (isZeroOid new))])
  | _ => none

/-- Decode a `git-receive-pack` request: the ref updates of a push. -/
def gitReceivePackDecoder : PureDecoder where
  name := "git-receive-pack"
  media := #["application/x-git-receive-pack-request"]
  step := fun buf complete =>
    match readPkts buf 0 (buf.size + 1) [] with
    | .malformed => .opaque
    | .frames pkts offset sawFlush =>
      let lines := payloads pkts
      if lines.isEmpty then (if complete then .opaque else .need (buf.size + 512))
      else if !sawFlush && !complete then .need (buf.size + 512)
      else
        let (first, caps) := splitCaps (lines.headD "")
        let all := first :: lines.tail
        -- A push certificate wraps the updates in a signed block; its lines are
        -- headers and a signature, not updates, and are reported as such.
        let signed := all.any fun l => l.startsWith "-----BEGIN PGP" || l == "push-cert"
        let updates := all.filterMap refUpdate
        .done (.map [
          (.str "kind", .str "receive-pack"),
          (.str "capabilities", .array (caps.map Value.str)),
          (.str "updates", .array updates),
          (.str "update_count", .integer updates.length),
          (.str "signed", .bool signed)]) offset

/-- Decode a `git-upload-pack` request: what a fetch or clone is asking for. -/
def gitUploadPackDecoder : PureDecoder where
  name := "git-upload-pack"
  media := #["application/x-git-upload-pack-request"]
  step := fun buf complete =>
    match readPkts buf 0 (buf.size + 1) [] with
    | .malformed => .opaque
    | .frames pkts offset sawFlush =>
      let lines := payloads pkts
      if lines.isEmpty then (if complete then .opaque else .need (buf.size + 512))
      else if !sawFlush && !complete then .need (buf.size + 512)
      else
        let (first, caps) := splitCaps (lines.headD "")
        let all := first :: lines.tail
        -- Version 2 states its command first; version 0 goes straight to wants.
        match all.findSome? (fun l =>
            if l.startsWith "command=" then some (Str.stripPrefix l "command=") else none) with
        | some command =>
          let args := all.filter fun l => !l.startsWith "command=" && !l.isEmpty
          let wants := args.filterMap fun l =>
            if l.startsWith "want " then some (Value.str (Str.stripPrefix l "want ")) else none
          let prefixes := args.filterMap fun l =>
            if l.startsWith "ref-prefix " then
              some (Value.str (Str.stripPrefix l "ref-prefix ")) else none
          .done (.map [
            (.str "kind", .str "v2"),
            (.str "command", .str command),
            (.str "args", .array (args.map Value.str)),
            (.str "wants", .array wants),
            (.str "ref_prefixes", .array prefixes)]) offset
        | none =>
          let wants := all.filterMap fun l =>
            if l.startsWith "want " then
              some (Value.str ((Str.stripPrefix l "want ").splitOn " " |>.headD "")) else none
          let haves := all.filterMap fun l =>
            if l.startsWith "have " then some (Value.str (Str.stripPrefix l "have ")) else none
          .done (.map [
            (.str "kind", .str "upload-pack"),
            (.str "capabilities", .array (caps.map Value.str)),
            (.str "wants", .array wants),
            (.str "want_count", .integer wants.length),
            (.str "haves", .array haves),
            (.str "done", .bool (all.contains "done"))]) offset

end Wire
end Kleis
