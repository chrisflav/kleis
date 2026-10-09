import Kleis.Policy.Grant
import Kleis.Policy.Externs
import Kleis.Facts.Flatten

/-!
# The decision

Everything the proxy knows about a request is turned into datalog here, and
biscuit decides.  The stage is pure: the same inputs give the same answer,
which is what makes the audit log replayable and what makes the properties in
the design statable at all.

## Who contributes what

| Contributor | Kind | Meaning |
| --- | --- | --- |
| primitive facts | facts | what arrived |
| body facts | facts | what it says |
| manifest | facts, rules | what it *is* |
| grant | facts, rules, checks, policies | what may be done |
| token authority | facts, checks | which grant, whose, until when |
| token blocks | checks | the bearer's own narrowing |

Biscuit's evaluation order does the rest: every check from every block must
pass, and a block can only ever add checks.  Attenuation is therefore monotone
by construction — a derived token cannot authorize anything its parent would
not — which is the property the whole offline-attenuation story rests on.

## The two guards this stage adds

`check if body_truncated(false)` is imposed by the authorizer rather than left
to the grant.  A body too large to flatten is a body nobody has read, and a
check is order-independent in a way a policy is not: it must pass whichever
`allow` matched.

`deny if true` is appended last, so a grant whose policies all fail to match
denies rather than falling through.
-/

namespace Kleis
namespace Policy

open LeanBiscuit
open LeanBiscuit.Datalog (Value)
open LeanBiscuit.Token (Biscuit AuthorizerBuilder Authorizer)

/-- What the decoder made of the request body. -/
inductive Body where
  /-- There was no body. -/
  | absent
  /-- There was one, and no decoder was configured for its media type. -/
  | opaque
  /-- There was one, a decoder was configured, and it could not read it. -/
  | undecodable
  /-- There was one, and this is what it says. -/
  | value (v : Value)
  deriving Inhabited

/-- The decoded value, if there is one. -/
def Body.value? : Body → Option Value
  | .value v => some v
  | _ => none

/-- Classify a body from what was configured and what came back.

The three-way distinction is the point: no body at all, a body nobody was asked
to read, and a body somebody was asked to read and could not. -/
def Body.classify (configured hasBody : Bool) (decoded : Option Value) : Body :=
  if !hasBody then .absent
  else match decoded with
    | some v => .value v
    | none => if configured then .undecodable else .opaque

/-- Everything the decision depends on. -/
structure Input where
  /-- The request. -/
  request : Model.Request
  /-- Its body, as decoded. -/
  body : Body
  /-- The service manifest. -/
  manifest : Service.Manifest
  /-- The grant the token claims. -/
  grant : Grant
  /-- The token, already verified against the root key. -/
  token : Biscuit
  /-- Revocation identifiers currently in force, hex encoded. -/
  revoked : List String
  /-- The current time, in seconds since the epoch. -/
  now : Nat
  /-- The client's address, for `client_ip`. -/
  clientIp : String
  /-- This request's identifier, for the audit log. -/
  requestId : String
  /-- Facts remembered for this token from earlier requests that succeeded — a
  repository it created — asserted as the authorizer's own. -/
  remembered : List Facts.Fact := []
  deriving Inhabited

/-- The outcome of a decision. -/
inductive Decision where
  /-- An `allow` policy at this index matched and every check passed. -/
  | allow (policy : Nat)
  /-- Refused, with a reason fit to be quoted back to the client. -/
  | deny (reason : String) (failedChecks : List String)
  deriving Repr, Inhabited

/-- A request that has been authorized.

The constructor is private to this module, and `Kleis.Proxy.Upstream.send`
takes a value of this type.  Forwarding a credential without a decision is
therefore not a mistake to be avoided by review; it is a program that does not
compile. -/
structure AuthorizedRequest where
  private mk ::
  /-- The request as it will be sent. -/
  request : Model.Request
  /-- The manifest that interpreted it, and whose credential host binding
  governs where it may go. -/
  manifest : Service.Manifest
  /-- The grant that allowed it. -/
  grant : Grant
  /-- The index of the `allow` policy that matched. -/
  policy : Nat
  /-- Whether a matching route asked for the response to be checked. -/
  responseGated : Bool
  /-- The credential to spend, or `none` to forward without one, as the grant
  chose it (`Grant.chooseCredential`). -/
  credential : Option String

/-- Everything a decision produced, for the audit log and for the client. -/
structure Outcome where
  /-- What was decided. -/
  decision : Decision
  /-- Every fact the authorizer was given, rendered as datalog. -/
  facts : List String
  /-- The token's revocation identifiers, hex encoded. -/
  revocationIds : List String
  /-- The authorization, when there was one. -/
  authorized : Option AuthorizedRequest

/-- Render the failed checks of a token error, for a message the bearer can
act on. -/
private def failedChecks : TokenError → List String
  | .failedLogic (.unauthorized _ checks) | .failedLogic (.noMatchingPolicy checks) =>
    checks.map fun c => match c with
      | .authorizer _ rule => s!"authorizer: {rule}"
      | .block id _ rule => s!"block {id}: {rule}"
  | _ => []

/-- The facts a body contributes. -/
def bodyFacts (b : Body) (limit : Nat) : List Facts.Fact :=
  match b with
  | .absent => Facts.emptyBody
  | .opaque => Facts.bodyPresent ++ Facts.opaqueBody
  | .undecodable => Facts.bodyPresent ++ Facts.undecodableBody
  | .value v => Facts.bodyPresent ++ Facts.transparentBody ++ Facts.ofBody v limit

/-- Assemble the authorizer for a request. -/
def assemble (i : Input) : AuthorizerBuilder :=
  let bodyValue := i.body.value?
  let facts :=
    Facts.ofRequest i.request
      ++ Facts.ambient i.now i.clientIp i.requestId
      ++ bodyFacts i.body i.manifest.maxBodyFacts
      ++ i.manifest.contribute i.request bodyValue
      ++ i.remembered
      ++ i.grant.facts
  -- Two guards the authorizer imposes rather than leaving to the grant.  Both
  -- are checks rather than policies, because a check is order-independent: it
  -- must pass whichever `allow` matched.
  let guard (predicate : String) : Builder.Check :=
    { queries := [{ head := ⟨"query", []⟩,
                    body := [⟨predicate, [.bool false]⟩],
                    expressions := [], scopes := [] }],
      kind := .one }
  -- A body too large to flatten is a body nobody has read.
  let truncationGuard := guard "body_truncated"
  -- A body a configured decoder could not read is worse: the manifest said
  -- what these bytes are and they are not.  Without this, every `reject if`
  -- over body facts is vacuously satisfied by a body nobody could parse — and
  -- `reject if` is exactly what a grant should be using, because `check all`
  -- refuses requests that legitimately carry no such facts at all.
  let decodabilityGuard := guard "body_undecodable"
  { facts
    rules := i.manifest.rules ++ i.grant.rules
    checks := truncationGuard :: decodabilityGuard :: i.grant.checks
    scopes := []
    policies := i.grant.policies ++
      [{ queries := [{ head := ⟨"query", []⟩, body := [], expressions := [],
                       scopes := [] }],
         kind := .deny }]
    externs := standard
    limits := {} }

/-- The credentials the evaluation derived with `use_credential(name)`, from
facts whose every origin is trusted: the authorizer — grant and manifest — and
the token's authority block.

The origin matters.  A bearer can append blocks of their own, and while biscuit
keeps the facts and rules in them from satisfying the authorizer's checks, they
still appear in the evaluated world: a block saying `use_credential("admin")`
would otherwise pick the credential its request went out on. -/
def derivedCredentials (dump : LeanBiscuit.Token.Authorizer.WorldDump) : List String :=
  dump.facts.flatMap fun (origins, facts) =>
    if !origins.all (fun o => o == none || o == some 0) then []
    else facts.filterMap fun f =>
      let pre := "use_credential(\""
      if f.startsWith pre && f.endsWith "\")" then
        some ((f.drop pre.length).dropEnd 2).toString
      else none

/-- Decide.

The revocation check comes first and does not involve datalog: a revoked token
is not a token whose policies happened not to match, and the distinction should
survive into the log. -/
def run (i : Input) : Outcome :=
  let revocationIds := (Token.Biscuit.revocationIdentifiers i.token).map Bytes.toHex
  let hit := revocationIds.filter fun id => i.revoked.contains id
  if !hit.isEmpty then
    { decision := .deny s!"the token is revoked ({(hit.headD "")})" []
      facts := [], revocationIds, authorized := none }
  else
    let builder := assemble i
    match Authorizer.build builder i.token with
    | .error e =>
      { decision := .deny (TokenError.toString e) (failedChecks e)
        facts := [], revocationIds, authorized := none }
    | .ok a =>
      let (result, final) := Authorizer.authorizeWithState a
      let dump := Authorizer.dumpWorld final
      let facts := dump.facts.flatMap (·.2)
      match result with
      | .error e =>
        { decision := .deny (TokenError.toString e) (failedChecks e)
          facts, revocationIds, authorized := none }
      | .ok policy =>
        let resources := i.manifest.resourcesOf
          (i.manifest.contribute i.request i.body.value? ++ i.remembered)
        let credential := i.grant.chooseCredential resources (derivedCredentials dump)
        { decision := .allow policy
          facts, revocationIds
          authorized := some (AuthorizedRequest.mk i.request i.manifest i.grant policy
            (i.manifest.gatesResponse i.request i.body.value?) credential) }

/-- Was this allowed? -/
def Outcome.allowed (o : Outcome) : Bool :=
  match o.decision with | .allow _ => true | .deny _ _ => false

/-- The reason a request was refused, for the body of the `403`. -/
def Outcome.reason (o : Outcome) : String :=
  match o.decision with
  | .allow i => s!"allowed by policy {i}"
  | .deny r checks =>
    if checks.isEmpty then r
    else r ++ "\n" ++ String.join (checks.map fun c => s!"  failed: {c}\n")

end Policy
end Kleis
