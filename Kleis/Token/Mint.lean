import Kleis.Service.Registry
import Kleis.Token.Revocation

/-!
# Minting a token, from a person or from an issuer

The one path both `kleis token issue` and the daemon's `/.kleis/v1/tokens` take,
so that what a token may claim is checked the same way whoever asked for it:
every grant it names exists, and it lives no longer than the shortest-lived of
them allows.  What an *issuer* may ask for on top of that is narrowed by the
daemon before it gets here (`Kleis.Proxy.Admin`).
-/

namespace Kleis
namespace Token

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- What is being asked for. -/
structure MintRequest where
  /-- The grants the token claims, in the order they are to be tried. -/
  grants : List String
  /-- Who will hold it. -/
  bearer : String
  /-- How long it should live, in seconds. -/
  ttl : Nat
  /-- Facts for its authority block. -/
  facts : List Builder.Fact := []
  /-- Make it an issuer's credential rather than a bearer token. -/
  issuer : Option String := none
  /-- The issuer asking, when one is. -/
  issuedBy : Option String := none

/-- Check a request against the grants it names, and mint it.  The token is
recorded so it can be listed and revoked; the token itself is not kept. -/
def mint (registry : Service.Registry) (r : MintRequest) :
    IO (Except String (Biscuit × IssuedRecord)) := do
  if r.issuer.isSome && !r.grants.isEmpty then
    return .error "an issuer's credential names no grants: it asks for tokens, it does not spend credentials"
  if r.issuer.isNone && r.grants.isEmpty then
    return .error "a token needs at least one grant"
  for name in r.grants do
    match registry.grant? name with
    | none => return .error s!"no such grant `{name}`"
    | some g =>
      if r.ttl > g.maxLifetime then
        return .error s!"the grant `{name}` allows tokens of at most {g.maxLifetime}s"
  let root ← loadOrCreateRootKey
  let ephemeral ← match PrivateKey.ofBytes .ed25519 (← Store.randomBytes 32) with
    | .ok k => pure k
    | .error e => return .error e.toString
  let now ← Store.now
  match issue root { grants := r.grants, bearer := r.bearer, lifetime := r.ttl
                     issuer := r.issuer, issuedBy := r.issuedBy, extraFacts := r.facts }
      now ephemeral with
  | .error e => return .error e
  | .ok (token, record) =>
    recordIssued record
    return .ok (token, record)

end Token
end Kleis
