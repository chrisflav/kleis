import Auth.Model.Request

/-!
# Body decoders

A decoder turns the leading bytes of an entity body into a datalog value.  It
is handed a growing prefix and answers "not yet", "here it is", or "this is not
something I can see into".

Prefix decoding is a requirement, not an optimisation.  A `git push` is a
packfile of arbitrary size whose ref updates sit in the first few hundred
bytes; a decoder that had to see the whole body would make the proxy buffer
every push before it could decide whether to allow it.  So `step` gets what has
arrived so far, says whether it needs more, and the rest of the body is never
held in memory at all.

The decision to buffer is therefore the decoder's, bounded by
`maxPrefix` — and a body that is still undecided at the bound is `opaque`,
which yields no facts and, given the deny preamble the authorizer appends,
no authority to do anything body-dependent.
-/

namespace Auth
namespace Wire

open LeanBiscuit (Bytes)
open LeanBiscuit.Datalog (Value)

/-- What a decoder makes of a prefix. -/
inductive Decoded where
  /-- Undecided: feed at least this many bytes in total before asking again.
  A decoder that simply wants the complete body asks for `bodySize`. -/
  | need (atLeast : Nat)
  /-- Decoded, accounting for this many bytes of the entity.  The remainder —
  a packfile, say — is relayed without being looked at. -/
  | done (value : Value) (consumed : Nat)
  /-- Structurally undecodable, or decodable only beyond the prefix bound. -/
  | opaque
  deriving Inhabited

/-- A decoder that needs nothing from the outside world. -/
structure PureDecoder where
  /-- The name a manifest refers to it by. -/
  name : String
  /-- The media types it claims by default. -/
  media : Array String
  /-- Decode a prefix.  The flag says whether the prefix is the whole body. -/
  step : Bytes → Bool → Decoded

/-- A decoder as a manifest may name one. -/
inductive Decoder where
  /-- One of the shipped decoders. -/
  | pure (d : PureDecoder)
  /-- A subprocess: the prefix on its standard input, JSON on its standard
  output.  The escape hatch for a format nobody has written Lean for, and it
  pays a process per request, so it is for the long tail. -/
  | exec (command : String) (args : List String)
  /-- Look at nothing. -/
  | opaque

/-- Was a decoder actually configured for this body?

`opaque` means nobody was asked to look, which is an ordinary situation for a
service whose bodies no policy cares about.  Anything else means the manifest
claimed to know what these bytes are — and if the decoder then fails, that is a
malformed request rather than an uninteresting one. -/
def Decoder.configured : Decoder → Bool
  | .opaque => false
  | _ => true

/-- The name a decoder is configured under. -/
def Decoder.name : Decoder → String
  | .pure d => d.name
  | .exec c _ => s!"exec:{c}"
  | .opaque => "none"

/-- A decoder that never looks at anything. -/
def opaqueDecoder : PureDecoder where
  name := "none"
  media := #[]
  step := fun _ _ => .opaque

end Wire
end Auth
