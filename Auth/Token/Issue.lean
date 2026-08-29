import Auth.Policy.Grant
import Auth.Store

/-!
# Issuing and attenuating tokens

The service is the biscuit root: it holds the private key, and every token it
issues carries an authority block naming the grant, the bearer and an expiry.

## Built, not printed

The authority block is assembled from `Builder.Fact` values rather than by
interpolating a bearer's name into datalog source and parsing it.  A bearer
called `x"); admin("` would otherwise write its own authority.  This is the
same rule as for route templates, for the same reason.

## Attenuation is the bearer's, not ours

`attenuate` needs no key and no server: appending a block requires only the
token, which is what makes it possible to narrow a token on a laptop before
handing it to a build.  Everything a block can add is a *check*, so a derived
token can only ever authorize less.
-/

namespace Auth
namespace Token

open LeanBiscuit
open LeanBiscuit.Token

/-- Where the root private key lives. -/
def rootKeyPath : IO System.FilePath := do return (← Dirs.data) / "root.key"

/-- Load the root key, generating one on first use. -/
def loadOrCreateRootKey : IO PrivateKey := do
  let path ← rootKeyPath
  let bytes ← match ← Store.readBin? path with
    | some b => pure b
    | none => do
      let b ← Store.randomBytes 32
      Store.writeSecret path b
      pure b
  match PrivateKey.ofBytes .ed25519 bytes with
  | .ok k => return k
  | .error e => throw (IO.userError s!"the root key is unusable: {e.toString}")

/-- The root public key, which is what a verifier needs and what `auth
root-key` prints. -/
def rootPublicKey : IO PublicKey := do
  match (← loadOrCreateRootKey).publicKey with
  | .ok k => return k
  | .error e => throw (IO.userError s!"the root key is unusable: {e.toString}")

/-- What a token is being issued for. -/
structure Issue where
  /-- The grant the token claims. -/
  grant : String
  /-- Who holds it, recorded as a fact so a policy can name them. -/
  bearer : String
  /-- How long it lives, in seconds. -/
  lifetime : Nat
  /-- Extra facts, already parsed, that the caller wants in the authority
  block. -/
  extraFacts : List Builder.Fact := []
  /-- Extra checks, already parsed. -/
  extraChecks : List Builder.Check := []

/-- The expiry check: `check if time($t), $t < <expiry>`.

Built rather than parsed, and expressed as a check rather than trusted to the
server, because a check travels with the token: whoever verifies it enforces
the expiry, including an attenuated copy the issuer never sees again. -/
def expiryCheck (expiry : Nat) : Builder.Check :=
  { queries := [{
      head := ⟨"query", []⟩
      body := [⟨"time", [.variable "t"]⟩]
      expressions := [{ ops := [.value (.variable "t"), .value (.date expiry),
                                .binary .lessThan] }]
      scopes := [] }]
    kind := .one }

/-- The authority block for an issue. -/
def authorityBlock (i : Issue) (expiry : Nat) : BlockBuilder :=
  { facts := [⟨⟨"grant", [.str i.grant]⟩⟩, ⟨⟨"bearer", [.str i.bearer]⟩⟩] ++ i.extraFacts
    rules := []
    checks := expiryCheck expiry :: i.extraChecks
    scopes := []
    context := none }

/-- A record of a token that was issued, kept so that it can be listed and
revoked.  The token itself is not kept: the daemon does not need it, and a
store of live bearer tokens is a store of things worth stealing. -/
structure IssuedRecord where
  /-- The token's revocation identifiers, hex. -/
  revocationIds : List String
  /-- The grant it claims. -/
  grant : String
  /-- Who it was issued to. -/
  bearer : String
  /-- When it was issued. -/
  issued : Nat
  /-- When it expires. -/
  expires : Nat

/-- Render an issued record. -/
def IssuedRecord.toJson (r : IssuedRecord) : Json :=
  .obj [("revocation_ids", .arr (r.revocationIds.map Json.str)),
        ("grant", .str r.grant), ("bearer", .str r.bearer),
        ("issued", .num (toString r.issued)), ("expires", .num (toString r.expires))]

/-- Read an issued record. -/
def IssuedRecord.ofJson (j : Json) : Except String IssuedRecord := do
  pure { revocationIds := (j.arr? "revocation_ids").filterMap Json.asString?
         grant := (j.str? "grant").getD ""
         bearer := (j.str? "bearer").getD ""
         issued := ((j.int? "issued").getD 0).toNat
         expires := ((j.int? "expires").getD 0).toNat }

/-- Issue a token, returning it and the record of it. -/
def issue (root : PrivateKey) (i : Issue) (now : Nat) (ephemeral : PrivateKey) :
    Except String (Biscuit × IssuedRecord) := do
  let expiry := now + i.lifetime
  let block := authorityBlock i expiry
  match Biscuit.create root ephemeral block with
  | .error e => throw (TokenError.toString e)
  | .ok token =>
    let record : IssuedRecord :=
      { revocationIds := (Biscuit.revocationIdentifiers token).map Bytes.toHex
        grant := i.grant, bearer := i.bearer, issued := now, expires := expiry }
    pure (token, record)

/-- Attenuate a token with further checks, written as datalog.

No key is needed beyond the one the token already carries, so this works
offline.  The source may only contain checks: a block that could add a *fact*
could satisfy a check the issuer meant to constrain it, which would make
attenuation a way to gain authority rather than shed it. -/
def attenuate (token : Biscuit) (source : String) (ephemeral : PrivateKey) :
    Except String Biscuit := do
  let parsed ← match Parser.parseBlock source with
    | .ok r => pure r
    | .error e => throw s!"could not parse the attenuation: {e}"
  if !parsed.facts.isEmpty then
    throw "an attenuation may only add checks, not facts"
  if !parsed.rules.isEmpty then
    throw "an attenuation may only add checks, not rules"
  if parsed.checks.isEmpty then
    throw "an attenuation with no checks would not narrow anything"
  let block : BlockBuilder := { checks := parsed.checks, scopes := parsed.scopes }
  match Biscuit.append token ephemeral block with
  | .ok t => pure t
  | .error e => throw (TokenError.toString e)

/-- The grant a token claims, read from the fact in its authority block.

This is needed *before* the authorizer can be built, because the grant is what
supplies the checks and policies — so it is read from the block directly rather
than queried out of a world that does not exist yet.

Only the authority block is consulted.  A `grant` fact in an appended block
would be the bearer choosing their own policy, which is the one thing
attenuation must not be able to do. -/
def grantOf? (token : Biscuit) : Option String := do
  let authority ← token.blocks.head?
  authority.facts.findSome? fun f =>
    match Builder.Predicate.convertFrom token.symbols f.predicate with
    | .ok p => if p.name == "grant" then
        match p.terms with
        | [.str g] => some g
        | _ => none
      else none
    | .error _ => none

/-- Who a token says it was issued to, for the log. -/
def bearerOf? (token : Biscuit) : Option String := do
  let authority ← token.blocks.head?
  authority.facts.findSome? fun f =>
    match Builder.Predicate.convertFrom token.symbols f.predicate with
    | .ok p => if p.name == "bearer" then
        match p.terms with
        | [.str b] => some b
        | _ => none
      else none
    | .error _ => none

/-- The text form of a token, as it is pasted into a proxy URL or an
environment variable. -/
def print (token : Biscuit) : String := Biscuit.toBase64 token

/-- Read a token from its text form, verifying it against the root key. -/
def parse (text : String) (root : PublicKey) : Except String Biscuit :=
  let text := Str.stripPrefix (Str.trim text) "biscuit:"
  match Biscuit.ofBase64 text root with
  | .ok t => .ok t
  | .error e => .error (TokenError.toString e)

end Token
end Auth
