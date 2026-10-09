import Kleis.Policy.Grant
import Kleis.Store

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

namespace Kleis
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

/-- The root public key, which is what a verifier needs and what `kleis
root-key` prints. -/
def rootPublicKey : IO PublicKey := do
  match (← loadOrCreateRootKey).publicKey with
  | .ok k => return k
  | .error e => throw (IO.userError s!"the root key is unusable: {e.toString}")

/-- What a token is being issued for. -/
structure Issue where
  /-- The grants the token claims, in the order the proxy tries them.

  More than one is how a bearer that works across services — a git host and an
  issue tracker — carries one token rather than one per service, and how one
  service can be reached on two credentials: a grant spending a bot's
  installation token for its own fork and another spending a person's token for
  the upstream it opens pull requests on.  Each grant is still decided on its
  own; see `Kleis.Policy.Select`. -/
  grants : List String
  /-- Who holds it, recorded as a fact so a policy can name them. -/
  bearer : String
  /-- How long it lives, in seconds. -/
  lifetime : Nat
  /-- Set when the token is itself an issuer's credential: `issuer(name)` in
  its authority, which is what `/.kleis/v1/tokens` asks for. -/
  issuer : Option String := none
  /-- The issuer that asked for this token, when one did.  Recorded as
  `issued_by(name)` so a grant can require it, and kept with the record so that
  an issuer may revoke what it issued and nothing else. -/
  issuedBy : Option String := none
  /-- Extra facts, already parsed and checked against `reservedPredicates`, that
  the caller wants in the authority block. -/
  extraFacts : List Builder.Fact := []
  /-- Extra checks, already parsed. -/
  extraChecks : List Builder.Check := []

/-- Predicates no extra fact may use.

The authority block is trusted, so a fact in it is believed by every grant.
These are the names the token itself, the proxy and the shipped manifests give
meaning to: a token carrying `operation("push")` or `repository("o", "r")`
would satisfy a grant's check for every request it made, whatever the request
was.  This list is the floor; an issuer is further confined to the predicates
its configuration names. -/
def reservedPredicates : List String :=
  ["grant", "bearer", "issuer", "issued_by", "time", "client_ip", "request_id",
   "operation", "repository", "pull_request", "issue", "ref_update", "creates_ref",
   "deletes_ref", "wants_object", "discover_service", "body", "request_body",
   -- The shipped GitHub manifest's vocabulary, for the same reason.
   "pr_head", "pr_base", "review_event", "review_comment_id", "label_added",
   "label_removed", "label_created", "organization", "new_repository",
   "repository_private", "graphql_operation", "created_repository",
   -- How a grant chooses which credential a request is spent on.
   "use_credential"]

/-- Is a predicate name one an extra fact may not use?  Every `request_*` and
`body_*` name is reserved along with the list, since those are what the proxy
emits for every request. -/
def isReservedPredicate (name : String) : Bool :=
  reservedPredicates.contains name || name.startsWith "request_" || name.startsWith "body_"
    || name.startsWith "response_"

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
  { facts := i.grants.map (fun g => ⟨⟨"grant", [.str g]⟩⟩)
      ++ [⟨⟨"bearer", [.str i.bearer]⟩⟩]
      ++ (i.issuer.map fun n => ⟨⟨"issuer", [.str n]⟩⟩).toList
      ++ (i.issuedBy.map fun n => ⟨⟨"issued_by", [.str n]⟩⟩).toList
      ++ i.extraFacts
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
  /-- The grants it claims. -/
  grants : List String
  /-- Who it was issued to. -/
  bearer : String
  /-- The issuer that asked for it, if one did. -/
  issuedBy : Option String := none
  /-- When it was issued. -/
  issued : Nat
  /-- When it expires. -/
  expires : Nat

/-- The grants, as one word for a listing. -/
def IssuedRecord.grantLabel (r : IssuedRecord) : String :=
  if r.grants.isEmpty then "-" else ",".intercalate r.grants

/-- Render an issued record. -/
def IssuedRecord.toJson (r : IssuedRecord) : Json :=
  .obj ([("revocation_ids", .arr (r.revocationIds.map Json.str)),
         ("grants", .arr (r.grants.map Json.str)), ("bearer", .str r.bearer),
         ("issued", .num (toString r.issued)), ("expires", .num (toString r.expires))]
        ++ (r.issuedBy.map fun n => ("issued_by", Json.str n)).toList)

/-- Read an issued record.  A record written before tokens could name more than
one grant has a single `grant`, which is read as a list of one. -/
def IssuedRecord.ofJson (j : Json) : Except String IssuedRecord := do
  let grants := match j.str? "grant" with
    | some g => [g]
    | none => (j.arr? "grants").filterMap Json.asString?
  pure { revocationIds := (j.arr? "revocation_ids").filterMap Json.asString?
         grants
         bearer := (j.str? "bearer").getD ""
         issuedBy := j.str? "issued_by"
         issued := ((j.int? "issued").getD 0).toNat
         expires := ((j.int? "expires").getD 0).toNat }

/-- Read one ground fact written as datalog: `task_repo("o", "r")`. -/
def factOfSource (src : String) : Except String Builder.Fact := do
  let src := Str.stripSuffix (Str.trim src) ";"
  match Parser.parseAuthorizer s!"{src};" with
  | .error e => throw s!"`{src}` is not a fact: {e}"
  | .ok r =>
    match r.facts, r.rules, r.checks, r.policies with
    | [f], [], [], [] => pure f
    | _, _, _, _ => throw s!"`{src}` is not a single fact"

/-- Turn a JSON value into a term: strings, integers and booleans as
themselves, and an array as a *set*, which is what a policy tests membership
in with `.contains`.  Nothing here is parsed as datalog, so a value cannot
smuggle in syntax whatever it contains. -/
partial def termOfJson : Json → Except String Builder.Term
  | .str s => pure (.str s)
  | .bool b => pure (.bool b)
  | .num raw =>
    match raw.toInt? with
    | some i => pure (.integer i)
    | none => throw s!"`{raw}` is not an integer"
  | .arr l => do
    let terms ← l.mapM termOfJson
    pure (.set (Builder.mkSet terms))
  | .null => throw "a fact cannot hold null"
  | .obj _ => throw "a fact cannot hold an object"

/-- Write a fact the way `factOfJson` reads it, for the terms a remembered fact
can hold: strings, integers and booleans.  `none` for anything else. -/
def factToJson? (f : Builder.Fact) : Option Json := do
  let terms ← f.predicate.terms.mapM fun t => match t with
    | .str s => some (Json.str s)
    | .integer i => some (Json.num (toString i))
    | .bool b => some (Json.bool b)
    | _ => none
  pure (.obj [("name", .str f.predicate.name), ("terms", .arr terms)])

/-- Read a fact from `{"name": "task_repo", "terms": ["o", "r"]}`. -/
def factOfJson (j : Json) : Except String Builder.Fact := do
  let some name := j.str? "name" | throw "a fact needs a `name`"
  if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '_' || c == ':') then
    throw s!"`{name}` is not a predicate name"
  let terms ← (j.arr? "terms").mapM termOfJson
  pure ⟨⟨name, terms⟩⟩

/-- Issue a token, returning it and the record of it. -/
def issue (root : PrivateKey) (i : Issue) (now : Nat) (ephemeral : PrivateKey) :
    Except String (Biscuit × IssuedRecord) := do
  for f in i.extraFacts do
    if isReservedPredicate f.predicate.name then
      throw s!"`{f.predicate.name}` is reserved and cannot be issued as a fact"
  let expiry := now + i.lifetime
  let block := authorityBlock i expiry
  match Biscuit.create root ephemeral block with
  | .error e => throw (TokenError.toString e)
  | .ok token =>
    let record : IssuedRecord :=
      { revocationIds := (Biscuit.revocationIdentifiers token).map Bytes.toHex
        grants := i.grants, bearer := i.bearer, issuedBy := i.issuedBy
        issued := now, expires := expiry }
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

/-- Every string `name(…)` holds in a token's authority block, in the order
the facts were written.

Only the authority block is consulted.  A `grant` fact in an appended block
would be the bearer choosing their own policy, which is the one thing
attenuation must not be able to do — and an attenuation cannot add facts in any
case, but this does not rely on that. -/
def authorityStrings (token : Biscuit) (name : String) : List String :=
  match token.blocks.head? with
  | none => []
  | some authority =>
    authority.facts.filterMap fun f =>
      match Builder.Predicate.convertFrom token.symbols f.predicate with
      | .ok p => if p.name == name then
          match p.terms with
          | [.str s] => some s
          | _ => none
        else none
      | .error _ => none

/-- The grants a token claims, read from the facts in its authority block, in
the order the proxy tries them.

This is needed *before* the authorizer can be built, because a grant is what
supplies the checks and policies — so it is read from the block directly rather
than queried out of a world that does not exist yet. -/
def grantsOf (token : Biscuit) : List String := authorityStrings token "grant"

/-- The first grant a token claims. -/
def grantOf? (token : Biscuit) : Option String := (grantsOf token).head?

/-- Who a token says it was issued to, for the log. -/
def bearerOf? (token : Biscuit) : Option String := (authorityStrings token "bearer").head?

/-- The issuer a token is the credential of, if it is one. -/
def issuerOf? (token : Biscuit) : Option String := (authorityStrings token "issuer").head?

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
end Kleis
