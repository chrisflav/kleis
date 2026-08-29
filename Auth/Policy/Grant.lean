import Auth.Util.Toml
import Auth.Service.Manifest

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

namespace Auth
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
  /-- The credential this grant spends. -/
  credential : String
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
  /-- The source, kept so `auth grant show` can print what was written rather
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
  let credential ← match j.str? "credential" with
    | some c => pure c
    | none => throw "a grant needs a `credential`"
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

end Policy
end Auth
