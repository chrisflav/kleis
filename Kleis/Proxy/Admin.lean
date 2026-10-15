import Kleis.Proxy.Forward
import Kleis.Token.Mint
import Kleis.Narrow
import Kleis.Card

/-!
# The daemon's own endpoints

Requests whose target is `/.kleis/…` are addressed to the daemon rather than
proxied anywhere.  They exist for one kind of client: a program that hands out
work and needs a token per job — an agent orchestrator, a CI runner — without
holding the root key.

```
GET  /.kleis/v1/health    any valid token
GET  /.kleis/v1/ca        any valid token: the interception CA, PEM
POST /.kleis/v1/tokens    an issuer's credential: mint a token
POST /.kleis/v1/derive    an issuer's credential: make a task token from a spec or a token
POST /.kleis/v1/revoke    an issuer's credential: revoke a token it minted or derived
GET  /.kleis/v1/setup     any valid token: what a sandbox needs to use it
GET  /.kleis/v1/card      any valid token: what it lets its bearer do, in prose
```

## Task tokens

`derive` makes a token for one task. From a **spec** the issuer may name (`[[issuer]]
specs`), it is a new token whose authority block kleis writes — `spec(…)`, the bearer, the
issuer, the task's facts vetted exactly as for `/tokens`, an expiry, and the narrowing — so a
grant reads the task's facts where it reads them today. From a **token** handed in, it is that
token with one more block holding only checks — the expiry and the narrowing — so it reaches
exactly what the token reached, minus what the block refuses; it carries no task facts, because
the token's holder decided what it reaches, not the issuer. An issuer's own credential is not
a source.

Either way the answer names one `revocation_id`, the block that tells this task token from
anything else, and the record kept for it holds that id alone: revoking it revokes this copy,
never the token it was made from.

## What an issuer may ask for

An issuer's credential is a biscuit with `issuer(name)` in its authority and no
grant, minted with `kleis issuer token`.  Everything it may put in a token is
bounded by its entry in `config.toml`, not by anything it sends: the grants it
may name, the predicates it may state facts with, and the longest a token may
live.  The proxy's own fact names are refused whatever that entry says
(`Token.reservedPredicates`), because a token stating `repository(…)` would
satisfy every grant's repository check.

A token minted here carries `issued_by(name)`, so a grant written for one
issuer's jobs can require it, and the record of it names the issuer, so that
one issuer may revoke what it minted and nothing else.

## Revocation takes effect at once

A revocation is written to the list on disk and to the daemon's copy of it in
the same step.  An orchestrator revokes a job's token when the job ends, and a
token that went on working until the next reload would make that a formality.
-/

namespace Kleis
namespace Proxy

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- Is this request for the daemon itself? -/
def isAdminTarget (target : String) : Bool := target.startsWith "/.kleis/"

/-- Answer with JSON and close. -/
private def respondJson (client : Net.Stream) (status : Nat) (body : Json) : IO Unit :=
  client.write (Http.simpleResponse status "application/json" (Json.render body ++ "\n"))

/-- Answer with an error and close. -/
private def respondError (client : Net.Stream) (status : Nat) (message : String) : IO Unit :=
  respondJson client status (.obj [("error", .str message)])

/-- Read a small request body in full. -/
private def readSmallBody (client : Net.Stream) (wire : Http.Request) (already : Bytes)
    (limit : Nat := 65536) : IO (Except String Bytes) := do
  match wire.framing with
  | .empty => return .ok ByteArray.empty
  | .length n =>
    if n > limit then return .error s!"the body is larger than {limit} bytes"
    let rest ← client.readExactly (n - min n already.size)
    let body := already ++ rest
    if body.size < n then return .error "the client closed mid-body"
    return .ok (Bytes.take body n)
  | _ => return .error "send the body with a Content-Length"

/-- The issuer a token is the credential of, checked against the configuration. -/
private def issuerFor (ctx : Context) (token : Biscuit) : Except String Issuer :=
  match Token.issuerOf? token with
  | none => .error "this needs an issuer's credential, and the token is not one"
  | some name =>
    match ctx.config.issuer? name with
    | none => .error s!"the issuer `{name}` is not configured"
    | some i => .ok i

/-- Read a duration given as seconds or as `8h`. -/
private def durationOf (j : Json) : Option Nat :=
  match j with
  | .num raw => raw.toNat?
  | .str s => Policy.parseDuration? s
  | _ => none

/-- `POST /.kleis/v1/tokens`. -/
private def mintFor (ctx : Context) (issuer : Issuer) (body : Json) :
    IO (Except (Nat × String) Json) := do
  let grants := (body.arr? "grants").filterMap Json.asString?
  if grants.isEmpty then return .error (400, "name at least one grant in `grants`")
  for g in grants do
    if !issuer.mayClaim g then
      return .error (403, s!"the issuer `{issuer.name}` may not issue the grant `{g}`")
  -- A `ttl` that does not parse is an error, not the maximum: "30 minutes" asked for less.
  let ttl ← match body.field? "ttl" with
    | none => pure issuer.maxTtl
    | some j => match durationOf j with
      | some t => pure t
      | none => return .error (400, "`ttl` is seconds or a duration such as `8h`")
  if ttl == 0 then return .error (400, "`ttl` must be positive")
  if ttl > issuer.maxTtl then
    return .error (403, s!"the issuer `{issuer.name}` may issue tokens of at most {issuer.maxTtl}s")
  let mut facts : List Builder.Fact := []
  for fj in body.arr? "facts" do
    match Token.factOfJson fj with
    | .error e => return .error (400, e)
    | .ok f =>
      let name := f.predicate.name
      if Token.isReservedPredicate name then
        return .error (403, s!"`{name}` is reserved and cannot be issued as a fact")
      if !issuer.mayState name then
        return .error (403, s!"the issuer `{issuer.name}` may not state `{name}` facts")
      facts := facts ++ [f]
  let bearer := (body.str? "bearer").getD s!"{issuer.name}:unnamed"
  match ← Token.mint (← ctx.registry.get)
      { grants, bearer, ttl, facts, issuedBy := some issuer.name } with
  | .error e => return .error (400, e)
  | .ok (token, record) =>
    return .ok (.obj [("token", .str (Token.print token)),
                      ("revocation_ids", .arr (record.revocationIds.map Json.str)),
                      ("expires", .num (toString record.expires))])

/-- The issued records of a token's blocks: its own expiry and narrowings, and those of
whatever it was derived from. -/
private def recordsOf (token : Biscuit) : IO (List Token.IssuedRecord) :=
  (Biscuit.revocationIdentifiers token).filterMapM fun id => Token.findIssuedExactly? (Bytes.toHex id)

/-- `POST /.kleis/v1/derive`. -/
private def deriveFor (ctx : Context) (issuer : Issuer) (body : Json) :
    IO (Except (Nat × String) Json) := do
  let registry ← ctx.registry.get
  let ttl ← match body.field? "ttl" with
    | none => pure issuer.maxTtl
    | some j => match durationOf j with
      | some t => pure t
      | none => return .error (400, "`ttl` is seconds or a duration such as `8h`")
  if ttl == 0 then return .error (400, "`ttl` must be positive")
  if ttl > issuer.maxTtl then
    return .error (403, s!"the issuer `{issuer.name}` may issue tokens of at most {issuer.maxTtl}s")
  let narrowings := (body.arr? "narrow").filterMap Json.asString?
  let checks ← match Narrow.compile registry narrowings with
    | .ok cs => pure cs
    | .error e => return .error (400, e)
  let bearer := (body.str? "bearer").getD s!"{issuer.name}:unnamed"
  let answer (token : Biscuit) (record : Token.IssuedRecord) : IO Json := do
    let card := Card.render registry token (← recordsOf token)
    return .obj [("token", .str (Token.print token)),
                 ("revocation_id", .str (record.revocationIds.headD "")),
                 ("revocation_ids", .arr (record.revocationIds.map Json.str)),
                 ("expires", .num (toString record.expires)),
                 ("card", .str card)]
  match body.str? "spec", body.str? "token" with
  | some _, some _ => return .error (400, "derive from a `spec` or from a `token`, not both")
  | none, none => return .error (400, "name a `spec` or give a `token` to derive from")
  | some spec, none =>
    if !issuer.maySpec spec then
      return .error (403, s!"the issuer `{issuer.name}` may not derive tokens from the spec `{spec}`")
    let mut facts : List Builder.Fact := []
    for fj in body.arr? "facts" do
      match Token.factOfJson fj with
      | .error e => return .error (400, e)
      | .ok f =>
        let name := f.predicate.name
        if Token.isReservedPredicate name then
          return .error (403, s!"`{name}` is reserved and cannot be issued as a fact")
        if !issuer.mayState name then
          return .error (403, s!"the issuer `{issuer.name}` may not state `{name}` facts")
        facts := facts ++ [f]
    match ← Token.mint registry
        { grants := [], specs := [spec], checks, narrowings, bearer, ttl, facts
          issuedBy := some issuer.name } with
    | .error e => return .error (400, e)
    | .ok (token, record) => return .ok (← answer token record)
  | none, some text =>
    if !(body.arr? "facts").isEmpty then
      return .error (400, "a task token derived from a token carries no facts; only its holder decides what it reaches")
    let parent ← match Token.parse text ctx.rootPublic with
      | .ok t => pure t
      | .error e => return .error (400, s!"the token to derive from was not accepted: {e}")
    if (Token.issuerOf? parent).isSome then
      return .error (403, "an issuer's credential is not something to derive a task token from")
    match ← tokenHolds ctx parent with
    | .error e => return .error (403, s!"the token to derive from does not hold: {e}")
    | .ok () => pure ()
    let now ← Store.now
    let expiry := now + ttl
    let block : LeanBiscuit.Token.BlockBuilder :=
      { checks := Token.expiryCheck expiry :: checks, scopes := [] }
    let ephemeral ← match PrivateKey.ofBytes .ed25519 (← Store.randomBytes 32) with
      | .ok k => pure k
      | .error e => return .error (500, e.toString)
    match Biscuit.append parent ephemeral block with
    | .error e => return .error (400, s!"could not derive: {TokenError.toString e}")
    | .ok token =>
      let some id := (Biscuit.revocationIdentifiers token).getLast?.map Bytes.toHex
        | return .error (500, "the derived token has no revocation id")
      let record : Token.IssuedRecord :=
        { revocationIds := [id], grants := [], specs := [], narrowings, bearer
          issuedBy := some issuer.name, issued := now, expires := expiry }
      Token.recordIssued record
      return .ok (← answer token record)

/-- `GET /.kleis/v1/setup`, for the bearer's own token. -/
private def setupFor (ctx : Context) (token : Biscuit) : IO (Except (Nat × String) Json) := do
  let registry ← ctx.registry.get
  match Card.setup registry token with
  | .error e => return .error (500, e)
  | .ok (env, files) =>
    let card := Card.render registry token (← recordsOf token)
    return .ok (.obj [
      ("proxy", .obj [("ca_pem", .str ctx.ca.root.pem)]),
      ("env", .obj (env.map fun (k, v) => (k, Json.str v))),
      ("files", .arr (files.map fun f => .obj ([("path", .str f.path), ("content", .str f.content)]
        ++ (f.mode.map fun m => ("mode", Json.str m)).toList))),
      ("no_proxy", .arr []),
      ("card", .str card)])

/-- `POST /.kleis/v1/revoke`. -/
private def revokeFor (ctx : Context) (issuer : Issuer) (body : Json) :
    IO (Except (Nat × String) Json) := do
  let some needle := body.str? "revocation_id"
    | return .error (400, "name the token by one of its `revocation_id`s")
  -- Exactly, not by prefix: a prefix is for a person at a shell, and a program
  -- that sent a short one would revoke whichever token happened to match.
  let some record ← Token.findIssuedExactly? needle
    | return .error (404, "no token with that revocation id was issued")
  if record.issuedBy != some issuer.name then
    return .error (403, s!"the issuer `{issuer.name}` did not issue that token")
  Token.revoke record.revocationIds
  ctx.revocations.modify fun r =>
    { r with ids := r.ids ++ record.revocationIds.filter (!r.ids.contains ·) }
  return .ok (.obj [("revoked", .arr (record.revocationIds.map Json.str))])

/-- Serve one request addressed to the daemon. -/
def handleAdmin (ctx : Context) (client : Net.Stream) (wire : Http.Request) (rest : Bytes)
    (token : Biscuit) (clientIp : String) : IO Unit := do
  match ← tokenHolds ctx token with
  | .error e => respondError client 407 s!"the token was not accepted: {e}"
  | .ok () =>
  let path := Str.pathOnly wire.target
  match wire.method, path with
  | "GET", "/.kleis/v1/health" => respondJson client 200 (.obj [("ok", .bool true)])
  | "GET", "/.kleis/v1/ca" =>
    client.write (Http.simpleResponse 200 "application/x-pem-file" ctx.ca.root.pem)
  | "GET", "/.kleis/v1/card" =>
    let card := Card.render (← ctx.registry.get) token (← recordsOf token)
    client.write (Http.simpleResponse 200 "text/plain; charset=utf-8" card)
  | "GET", "/.kleis/v1/setup" =>
    match ← setupFor ctx token with
    | .error (status, message) => respondError client status message
    | .ok answer => respondJson client 200 answer
  | "POST", "/.kleis/v1/tokens" | "POST", "/.kleis/v1/revoke" | "POST", "/.kleis/v1/derive" =>
    match issuerFor ctx token with
    | .error e => respondError client 403 e
    | .ok issuer =>
      match ← readSmallBody client wire rest with
      | .error e => respondError client 400 e
      | .ok bytes =>
        match Json.parse (Bytes.toStringLossy bytes) with
        | .error e => respondError client 400 s!"the body is not JSON: {e}"
        | .ok body =>
          let result ← if path == "/.kleis/v1/tokens" then mintFor ctx issuer body
            else if path == "/.kleis/v1/derive" then deriveFor ctx issuer body
            else revokeFor ctx issuer body
          match result with
          | .error (status, message) => respondError client status message
          | .ok answer =>
            if ctx.config.audit then
              ctx.audit.append {
                time := ← Store.now, requestId := ← ctx.nextRequestId
                method := wire.method, url := path, clientIp
                service := "kleis", manifestVersion := "", grant := s!"issuer:{issuer.name}"
                grantVersion := ""
                revocationIds := (Biscuit.revocationIdentifiers token).map Bytes.toHex
                allowed := true
                -- What was minted or revoked, but never the minted token.
                outcome := Json.render (match answer with
                  | .obj fs => .obj (fs.filter (·.1 != "token"))
                  | other => other)
                facts := [], credential := none, status := some 200 }
            respondJson client 200 answer
  | _, _ => respondError client 404 s!"no such endpoint `{wire.method} {path}`"

end Proxy
end Kleis
