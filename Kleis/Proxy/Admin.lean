import Kleis.Proxy.Forward
import Kleis.Token.Mint

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
POST /.kleis/v1/revoke    an issuer's credential: revoke a token it minted
```

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
  | "POST", "/.kleis/v1/tokens" | "POST", "/.kleis/v1/revoke" =>
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
