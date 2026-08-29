import Auth.Credential.Store
import Auth.Net.Client

/-!
# Credential providers

A provider turns stored material into a secret that can be spent right now.
Four of them, and the fourth is why the design says a new provider usually
costs a file rather than Lean:

- `static` — a personal access token, an API key.  The material *is* the
  secret.
- `exec` — run a command, read the secret from its standard output.  Any
  credential obtainable by a shell command needs no code here at all.
- `oauth2` — a refresh token exchanged for an access token, cached until
  shortly before it expires.
- `github-app` — an installation token, signed for with the app's private key
  and minted per repository where the grant asks for it.

The last two exist because they are common enough to be worth refreshing
properly rather than shelling out to something that re-authenticates on every
request.

## Narrowing

Where a provider can mint a *narrower* credential than the one it holds — an
installation token scoped to one repository — the grant may ask it to.  Then
the credential that leaves the building is already attenuated even if the proxy
is later bypassed: the datalog is the fine-grained control, the minted scope is
the coarse one, and neither is relied on alone.
-/

namespace Auth
namespace Credential

open LeanBiscuit

/-- A secret together with when it stops being usable. -/
structure Live where
  /-- The secret. -/
  secret : Secret
  /-- When it expires, if it does. -/
  expires : Option Nat

/-- Is this still usable, with a margin so that a token does not expire
between the check and the request it is used in? -/
def Live.fresh (l : Live) (now : Nat) (margin : Nat := 60) : Bool :=
  match l.expires with
  | none => true
  | some e => now + margin < e

/-- The cache of live credentials, keyed by the credential name and whatever
narrowing was asked for. -/
structure Cache where
  /-- Name and narrowing key, to the live secret. -/
  entries : IO.Ref (Array (String × Live))

/-- An empty cache. -/
def Cache.create : IO Cache := do return { entries := ← IO.mkRef #[] }

/-- Read the material of a `static` credential: the whole thing, trimmed, since
a token pasted into a terminal usually arrives with a newline. -/
private def staticSecret (material : Secret) : Secret :=
  Secret.ofString (Str.trim (Bytes.toStringLossy (Secret.reveal material)))

/-- Run a command and take its standard output as the secret.

The material is passed on standard input rather than in the command line, so
it does not appear in the process table. -/
private def execSecret (config : Json) (material : Secret) : IO Live := do
  let some command := config.str? "command"
    | throw (IO.userError "an `exec` credential needs a `command`")
  let args := (config.arr? "args").filterMap Json.asString?
  let child ← IO.Process.spawn {
    cmd := command, args := args.toArray
    stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.write (Secret.reveal material)
  stdin.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then
    throw (IO.userError s!"`{command}` failed with status {code}: {Str.trim err}")
  let lifetime := ((config.int? "lifetime").getD 0).toNat
  let expires ← if lifetime == 0 then pure none else do pure (some ((← Store.now) + lifetime))
  return { secret := Secret.ofString (Str.trim out), expires }

/-- Exchange a refresh token for an access token. -/
private def oauth2Secret (ctx : Net.Tls.Context) (config : Json) (material : Secret) :
    IO Live := do
  let some endpoint := config.str? "token_endpoint"
    | throw (IO.userError "an `oauth2` credential needs a `token_endpoint`")
  let clientId := (config.str? "client_id").getD ""
  -- The material is the refresh token, and the client secret if there is one.
  let materialJson := Bytes.toStringLossy (Secret.reveal material)
  let parsed := (Json.parse materialJson).toOption.getD (.obj [])
  let refresh := (parsed.str? "refresh_token").getD (Str.trim materialJson)
  let clientSecret := parsed.str? "client_secret"
  let form := String.intercalate "&" (
    ["grant_type=refresh_token", s!"refresh_token={Str.percentEncode refresh}"]
    ++ (if clientId.isEmpty then [] else [s!"client_id={Str.percentEncode clientId}"])
    ++ (match clientSecret with
        | some cs => [s!"client_secret={Str.percentEncode cs}"]
        | none => []))
  let response ← Net.fetch ctx "POST" endpoint
    #[("content-type", "application/x-www-form-urlencoded"), ("accept", "application/json")]
    (Bytes.ofString form)
  if response.status ≥ 300 then
    throw (IO.userError s!"the token endpoint answered {response.status}")
  let body ← match Json.parse response.text with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"the token endpoint returned malformed JSON: {e}")
  let some token := body.str? "access_token"
    | throw (IO.userError "the token endpoint returned no access_token")
  let expiresIn := ((body.int? "expires_in").getD 3600).toNat
  return { secret := Secret.ofString token, expires := some ((← Store.now) + expiresIn) }

/-- Mint a GitHub App installation token.

The app's JSON Web Token is signed with RS256 in the general case, which is not
in `lean-biscuit` — so the material here is expected to be an installation
token minter the owner has already set up, or the app's own token.  Where a
private key signature is needed, `exec` with `gh` or a two-line script is the
supported route, and is why that provider exists. -/
private def githubAppSecret (ctx : Net.Tls.Context) (config : Json) (material : Secret)
    (narrow : Json) : IO Live := do
  let installation := (config.int? "installation_id").getD 0
  if installation == 0 then
    throw (IO.userError "a `github-app` credential needs an `installation_id`")
  let api := (config.str? "api").getD "https://api.github.com"
  let url := s!"{api}/app/installations/{installation}/access_tokens"
  -- The narrowing the grant asked for, passed straight through to GitHub.
  let repositories := (narrow.arr? "repositories").filterMap Json.asString?
  let body := Json.render (.obj (
    (if repositories.isEmpty then []
     else [("repositories", Json.arr (repositories.map Json.str))])
    ++ (match narrow.field? "permissions" with
        | some p => [("permissions", p)]
        | none => [])))
  let jwt := Str.trim (Bytes.toStringLossy (Secret.reveal material))
  let response ← Net.fetch ctx "POST" url
    #[("authorization", s!"Bearer {jwt}"), ("accept", "application/vnd.github+json"),
      ("content-type", "application/json"), ("user-agent", "auth")]
    (Bytes.ofString body)
  if response.status ≥ 300 then
    throw (IO.userError s!"GitHub answered {response.status} minting an installation token")
  let parsed ← match Json.parse response.text with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"GitHub returned malformed JSON: {e}")
  let some token := parsed.str? "token"
    | throw (IO.userError "GitHub returned no token")
  -- Installation tokens last an hour; the expiry is returned but a fixed
  -- margin is enough and avoids depending on a timestamp format.
  return { secret := Secret.ofString token, expires := some ((← Store.now) + 3000) }

/-- The cache key for a credential and a narrowing. -/
private def cacheKey (name : String) (narrow : Json) : String :=
  s!"{name}\n{Json.render narrow}"

/-- Obtain a usable secret for a credential, refreshing or minting if what is
cached has expired. -/
def resolve (cache : Cache) (ctx : Net.Tls.Context) (record : Record) (narrow : Json) :
    IO Secret := do
  let now ← Store.now
  let key := cacheKey record.name narrow
  let entries ← cache.entries.get
  if let some (_, live) := Array.find? (fun (k, _) => k == key) entries then
    if live.fresh now then return live.secret
  let material ← unlock record
  let live ← match record.provider with
    | "static" => pure { secret := staticSecret material, expires := none }
    | "exec" => execSecret record.config material
    | "oauth2" => oauth2Secret ctx record.config material
    | "github-app" => githubAppSecret ctx record.config material narrow
    | other => throw (IO.userError s!"unknown credential provider `{other}`")
  cache.entries.modify fun es =>
    (Array.filter (fun (k, _) => k != key) es).push (key, live)
  return live.secret

/-- Forget everything cached, so that the next request re-mints.  What `auth
reload` does, and what a revoked upstream token needs. -/
def Cache.clear (c : Cache) : IO Unit := c.entries.set #[]

end Credential
end Auth
