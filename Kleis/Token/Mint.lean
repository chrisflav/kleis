import Kleis.Service.Registry
import Kleis.Token.Revocation
import Kleis.Config

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
  -- Beyond the fixed list, every name a loaded manifest gives meaning to — what its
  -- routes emit or remember, what its rules derive — and the one a grant chooses a
  -- credential with.  A token asserting any of them would be asserting what the
  -- proxy is meant to work out for itself.
  for f in r.facts do
    let n := f.predicate.name
    if n == "use_credential" || registry.manifests.any (·.vocabulary.contains n) then
      return .error s!"`{n}` is reserved and cannot be issued as a fact"
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

/-- Keep an issuer's credential in its `token_file`: leave a good one alone, mint a
new one otherwise.  "Good" is a token for this issuer that verifies against the
current root key, is not revoked, and is further from its expiry than a quarter
of `token_ttl` — so a long-running deployment renews it at a restart well before
it lapses, rather than finding out when the issuer is refused.

Written 0640, so that the one other account meant to read it can do so through
the group of the directory it is in, and nothing else can. -/
def ensureIssuerToken (registry : Service.Registry) (issuer : Issuer) : IO (Option String) := do
  let some path := issuer.tokenFile | return none
  let now ← Store.now
  let root ← rootPublicKey
  let revoked := (← loadRevocations).ids
  if let some text ← Store.read? path then
    if let .ok t := parse text root then
      if issuerOf? t == some issuer.name then
        let ids := (Biscuit.revocationIdentifiers t).map Bytes.toHex
        if !ids.any revoked.contains then
          if let some record ← findIssuedExactly? (ids.headD "") then
            if record.expires > now + issuer.tokenTtl / 4 then return none
  match ← mint registry { grants := [], bearer := s!"issuer:{issuer.name}"
                          ttl := issuer.tokenTtl, issuer := some issuer.name } with
  | .error e => throw (IO.userError s!"could not mint the credential of issuer `{issuer.name}`: {e}")
  | .ok (token, _) =>
    if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
    Store.writeWithMode path (Bytes.ofString (print token ++ "\n")) "640"
    return some path

end Token
end Kleis
