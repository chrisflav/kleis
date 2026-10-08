import Kleis.Util.Toml
import Kleis.Service.Manifest

/-!
# Grants

A grant is what the owner of a credential writes: the conditions under which
that credential may be spent, in datalog, and the ceiling on how long a token
naming it may live.

The grant is the only contributor that may `allow`.  A manifest describes what
a request *is*; a token says which grant it is claiming and narrows it further;
the grant decides.  Keeping the decision in one file, written by one party,
means "who can authorise this" has a one-word answer.
-/

namespace Kleis
namespace Policy

open LeanBiscuit

/-- Parse a duration: a number followed by `s`, `m`, `h` or `d`. -/
def parseDuration? (s : String) : Option Nat := do
  let s := Str.trim s
  if s.isEmpty then none else
    let unit := (s.takeEnd 1).toString
    let (numText, mult) :=
      match unit with
      | "s" => ((s.dropEnd 1).toString, 1)
      | "m" => ((s.dropEnd 1).toString, 60)
      | "h" => ((s.dropEnd 1).toString, 3600)
      | "d" => ((s.dropEnd 1).toString, 86400)
      | _ => (s, 1)
    let n ← numText.toNat?
    some (n * mult)

/-- A grant. -/
structure Grant where
  /-- The name a token claims. -/
  name : String
  /-- The service whose manifest interprets the request. -/
  service : String
  /-- The credential this grant spends, or `none` for a grant that forwards
  without one.

  An anonymous grant is for requests the upstream would serve to anybody — a
  public clone, a release download — which should not be made on somebody's
  credential merely because a manifest claims the host.  It has to be asked for
  (`anonymous = true`): a grant whose `credential` was simply left out is a
  mistake, and reading it as anonymous would turn a typo into requests that go
  out unauthenticated without anybody having decided they should. -/
  credential : Option String
  /-- The longest a token naming this grant may live, in seconds. -/
  maxLifetime : Nat
  /-- Facts the grant asserts. -/
  facts : List Builder.Fact
  /-- Rules the grant adds. -/
  rules : List Builder.Rule
  /-- The conditions every request must satisfy. -/
  checks : List Builder.Check
  /-- The policies that decide. -/
  policies : List Builder.Policy
  /-- Whether the credential provider should be asked to mint a narrowed
  credential, and with what arguments. -/
  narrow : Json
  /-- The SHA-256 of the source, hex, recorded with every decision. -/
  version : String
  /-- The source, kept so `kleis grant show` can print what was written rather
  than a re-rendering of it. -/
  source : String
  deriving Inhabited

/-- Read a grant from TOML source. -/
def Grant.ofToml (source : String) : Except String Grant := do
  let j ← Toml.parse source
  let name ← match j.str? "name" with
    | some n => pure n
    | none => throw "a grant needs a `name`"
  let service ← match j.str? "service" with
    | some s => pure s
    | none => throw "a grant needs a `service`"
  let credential ← match j.str? "credential", (j.bool? "anonymous").getD false with
    | some c, false => pure (some c)
    | none, true => pure none
    | some _, true => throw "a grant is either `anonymous` or names a `credential`, not both"
    | none, false => throw "a grant needs a `credential`, or `anonymous = true`"
  let maxLifetime ← match j.str? "max_lifetime" with
    | none => pure 86400
    | some d => match parseDuration? d with
      | some n => pure n
      | none => throw s!"`{d}` is not a duration"
  let datalog := (j.str? "datalog").getD ""
  let parsed ← match Parser.parseAuthorizer datalog with
    | .ok r => pure r
    | .error e => throw s!"in the grant's datalog: {e}"
  if parsed.policies.isEmpty then
    throw "a grant with no policy can never allow anything; add `allow if …`"
  pure {
    name, service, credential, maxLifetime
    facts := parsed.facts
    rules := parsed.rules
    checks := parsed.checks
    policies := parsed.policies
    narrow := (j.field? "narrow").getD (.obj [])
    version := Bytes.toHex (Sha256.hash (Bytes.ofString source))
    source
  }

/-- The credential, as a person reads it in a listing. -/
def Grant.credentialLabel (g : Grant) : String := g.credential.getD "(anonymous)"

end Policy
end Kleis
