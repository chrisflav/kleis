import Kleis.Credential.Store
import Kleis.Net.Client

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

namespace Kleis
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

/-- The cache of live credentials, keyed by the credential name, whatever
narrowing was asked for, and — for a `per_owner` App — the owner. -/
structure Cache where
  /-- Name and narrowing key, to the live secret. -/
  entries : IO.Ref (Array (String × Live))
  /-- Credential and owner, for a `per_owner` App found not to be installed on
  that owner, to when to ask GitHub again.  Without it an owner the App is not
  installed on would cost two lookups on every request for it. -/
  missing : IO.Ref (Array (String × Nat))

/-- An empty cache. -/
def Cache.create : IO Cache := do return { entries := ← IO.mkRef #[], missing := ← IO.mkRef #[] }

/-- How long an owner found to have no installation is believed to have none. -/
def missingInstallationTtl : Nat := 600

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

/-- A GitHub App's JSON Web Token, signed with its private key: the credential
it presents to ask for an installation token.  Back-dated a minute and valid for
nine, which is inside GitHub's ten and tolerant of a clock that is a little
fast. -/
private def githubAppJwt (appId : Nat) (keyPem : ByteArray) : IO String := do
  let now ← Store.now
  let header := Base64.encodeUrl (Bytes.ofString "{\"alg\":\"RS256\",\"typ\":\"JWT\"}")
  let payload := Base64.encodeUrl (Bytes.ofString
    s!"\{\"iat\":{now - 60},\"exp\":{now + 540},\"iss\":{appId}}")
  let unsigned := s!"{header}.{payload}"
  let signature ← Net.Tls.signRs256 keyPem (Bytes.ofString unsigned)
  return s!"{unsigned}.{Base64.encodeUrl signature}"

/-- Ask GitHub, as the App, which installation it has on an account — an
organisation or a user, tried in that order.  `none` when GitHub says it has
none on either. -/
private def githubAppInstallation (ctx : Net.Tls.Context) (api jwt owner : String) :
    IO (Option Nat) := do
  let headers := #[("authorization", s!"Bearer {jwt}"), ("accept", "application/vnd.github+json"),
                   ("user-agent", "kleis")]
  -- A 404 from both means no installation; anything else is a different problem —
  -- a JWT GitHub rejects, a rate limit — and is reported as what it is.
  let mut statuses : List Nat := []
  for kind in ["orgs", "users"] do
    let response ← Net.fetch ctx "GET" s!"{api}/{kind}/{Str.percentEncode owner}/installation" headers
    if response.status == 200 then
      if let .ok j := Json.parse response.text then
        if let some id := j.int? "id" then return some id.toNat
    statuses := statuses ++ [response.status]
  if statuses.all (· == 404) then return none
  throw (IO.userError s!"looking up the GitHub App's installation on `{owner}` failed: GitHub answered {statuses}")

/-- Could this be a GitHub account name: 1 to 39 letters, digits and hyphens.  An
owner that could not is never looked up — it would only cost two calls to learn
that GitHub has no such account — and the configured owner is used instead. -/
def isGitHubLogin (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 39 && s.all (fun c => c.isAlphanum || c == '-')

/-- Whether a `github-app` credential is minted per owner: `per_owner = true`,
and no `installation_id`, which fixes the installation whatever the owner. -/
def perOwner (config : Json) : Bool :=
  config.bool? "per_owner" == some true && (config.int? "installation_id").isNone

/-- How many owners without an installation are remembered at once.  Past it the
oldest is forgotten, so a bearer naming owner after owner cannot grow the list
without bound. -/
def missingInstallationCap : Nat := 1024

/-- A grant's `repositories` narrowing for a token minted on `owner`'s
installation.  A bare name means a repository of whichever installation is
minted, which for a `per_owner` App is any owner's — so there only `owner/repo`
entries are accepted, and those of other owners dropped.  `none` when nothing
the grant named is under this owner: the token would otherwise be unnarrowed. -/
def narrowRepositories (perOwner : Bool) (owner : Option String) (repositories : List String) :
    Except String (Option (List String)) :=
  if repositories.isEmpty then .ok (some [])
  else if !perOwner then .ok (some repositories)
  else if repositories.any (!·.contains '/') then
    .error "a `per_owner` App narrows by `owner/repo`, not by a bare repository name"
  else
    let mine := repositories.filterMap fun r =>
      match r.splitOn "/" with
      | [o, n] => if some o.toLower == owner.map (·.toLower) then some n else none
      | _ => none
    .ok (if mine.isEmpty then none else some mine)

/-- The account a GitHub App credential's installation is looked up on, for a
request about `requestOwner`.

An App is installed per account, and an installation token reaches only that
account's repositories.  A credential naming one `owner` therefore works for one
account; with `per_owner = true` it is looked up on the owner of the repository
the request is about instead — the job's fork in one organisation, its upstream
in another — and `owner` is what a request about no repository (GraphQL) uses.
`none` when the credential names neither an `installation_id` nor anything to
look one up on. -/
def installationOwner (config : Json) (requestOwner : Option String) : Option String :=
  let configured := config.str? "owner"
  if perOwner config then
    match requestOwner with
    | some o => if isGitHubLogin o then some o else configured
    | none => configured
  else configured

/-- Mint a GitHub App installation token.

The stored material is either the App's private key, PEM — in which case the
App's token is signed here, with `app_id` from the configuration, and the
installation is `installation_id` or else looked up on `owner` (see
`installationOwner`) — or, as before, an App token somebody else signed, which
is used as it is.  The key never leaves this function; what goes upstream is the
installation token, which lasts an hour and is cached until shortly before then.

An owner the App is not installed on is remembered in `missing` for
`missingInstallationTtl`, so that it is not asked about on every request, and is
`none`; `resolve` then uses the configured `owner`'s token instead. -/
private def githubAppSecret (ctx : Net.Tls.Context) (missing : IO.Ref (Array (String × Nat)))
    (name : String) (config : Json) (material : Secret) (narrow : Json) (owner : Option String) :
    IO (Option Live) := do
  let api := (config.str? "api").getD "https://api.github.com"
  let raw := Secret.reveal material
  let isPem := (Bytes.toStringLossy (Bytes.take raw 64)).trimAscii.toString.startsWith "-----BEGIN"
  let jwt ← if isPem then do
      let some appId := config.int? "app_id"
        | throw (IO.userError "a `github-app` credential holding a private key needs an `app_id`")
      githubAppJwt appId.toNat raw
    else pure (Str.trim (Bytes.toStringLossy raw))
  -- The installation on `o`, or `none` if there is none — remembered either way
  -- for as long as the answer is worth trusting.
  let lookup (o : String) : IO (Option Nat) := do
    let k := s!"{name}\n{o.toLower}"
    let now ← Store.now
    if (← missing.get).any (fun (k', due) => k' == k && now < due) then return none
    match ← githubAppInstallation ctx api jwt o with
    | some id => return some id
    | none =>
      missing.modify fun ms =>
        let kept := ms.filter fun (k', due) => k' != k && now < due
        let kept := if kept.size < missingInstallationCap then kept
          else kept.extract (kept.size + 1 - missingInstallationCap) kept.size
        kept.push (k, now + missingInstallationTtl)
      return none
  let configured := config.str? "owner"
  let (installation, mintedOn) ← match config.int? "installation_id" with
    | some id => pure (id.toNat, configured)
    | none =>
      match owner with
      | none => throw (IO.userError
          "a `github-app` credential needs an `installation_id`, or an `owner` to look one up on")
      | some o =>
        match ← lookup o with
        | some id => pure (id, some o)
        | none => return none
  let url := s!"{api}/app/installations/{installation}/access_tokens"
  -- The narrowing the grant asked for, for the installation the token is minted on.
  let repositories ← match narrowRepositories (perOwner config) mintedOn
      ((narrow.arr? "repositories").filterMap Json.asString?) with
    | .ok (some rs) => pure rs
    | .ok none => throw (IO.userError
        s!"the grant narrows the token to repositories none of which is under `{mintedOn.getD ""}`")
    | .error e => throw (IO.userError e)
  let body := Json.render (.obj (
    (if repositories.isEmpty then []
     else [("repositories", Json.arr (repositories.map Json.str))])
    ++ (match narrow.field? "permissions" with
        | some p => [("permissions", p)]
        | none => [])))
  let response ← Net.fetch ctx "POST" url
    #[("authorization", s!"Bearer {jwt}"), ("accept", "application/vnd.github+json"),
      ("content-type", "application/json"), ("user-agent", "kleis")]
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
  return some { secret := Secret.ofString token, expires := some ((← Store.now) + 3000) }

/-- The cache key for a credential, a narrowing and — where the credential is
minted per owner — the owner, lowercased, as GitHub compares account names. -/
def cacheKey (name : String) (narrow : Json) (owner : Option String := none) : String :=
  match owner with
  | some o => s!"{name}\n{Json.render narrow}\n{o.toLower}"
  | none => s!"{name}\n{Json.render narrow}"

/-- Obtain a usable secret for a credential, refreshing or minting if what is
cached has expired.  `requestOwner` is the owner of the repository the request
is about, which a `per_owner` GitHub App mints for.

For a `per_owner` App the request's owner is tried first and the configured
`owner` second, each through the cache: an owner the App is not installed on —
found out once, then remembered — is served from the configured owner's one token,
so a bearer naming owner after owner neither mints a token for each nor grows
the cache by one. -/
def resolve (cache : Cache) (ctx : Net.Tls.Context) (record : Record) (narrow : Json)
    (requestOwner : Option String := none) : IO Secret := do
  let now ← Store.now
  -- A static secret read from a file is read again each time: the file is the secret's
  -- home, and a rotation there should take effect on the next request rather than after
  -- a restart.  What a provider mints from it is still cached — an installation token
  -- lasts an hour whatever happens to the key it was minted with.
  if record.secretFile.isSome && record.provider == "static" then
    return staticSecret (← unlock record)
  let cached (key : String) : IO (Option Secret) := do
    match Array.find? (fun (k, _) => k == key) (← cache.entries.get) with
    | some (_, live) => return if live.fresh now then some live.secret else none
    | none => return none
  -- Expired entries go when something is stored, so the cache holds live tokens only.
  let store (key : String) (live : Live) : IO Unit :=
    cache.entries.modify fun es =>
      (Array.filter (fun (k, l) => k != key && l.fresh now 0) es).push (key, live)
  if record.provider == "github-app" then
    let keyed := perOwner record.config
    let configured := record.config.str? "owner"
    let asked := installationOwner record.config requestOwner
    -- Only a `per_owner` App's tokens differ by owner; any other is one token.
    let candidates : List (Option String) :=
      if !keyed then [asked]
      else if asked.map (·.toLower) == configured.map (·.toLower) then [configured]
      -- A missing configured owner is no fallback, and asking it would only report
      -- the credential as misconfigured instead of the owner as not installed.
      else match configured with
        | some _ => [asked, configured]
        | none => [asked]
    let known (o : String) : IO Bool := do
      let k := s!"{record.name}\n{o.toLower}"
      return (← cache.missing.get).any (fun (k', due) => k' == k && now < due)
    let mut material : Option Secret := none
    for c in candidates do
      let key := cacheKey record.name narrow (if keyed then c else none)
      if let some s ← cached key then return s
      -- Known to have no installation: straight to the next candidate.
      if keyed && c != configured then
        if let some o := c then
          if ← known o then continue
      let m ← match material with
        | some m => pure m
        | none => do let m ← unlock record; material := some m; pure m
      match ← githubAppSecret ctx cache.missing record.name record.config m narrow c with
      | some live => store key live; return live.secret
      | none => continue
    throw (IO.userError s!"the GitHub App has no installation on `{(asked.orElse fun _ => configured).getD ""}`")
  let key := cacheKey record.name narrow
  if let some s ← cached key then return s
  let material ← unlock record
  let live ← match record.provider with
    | "static" => pure { secret := staticSecret material, expires := none }
    | "exec" => execSecret record.config material
    | "oauth2" => oauth2Secret ctx record.config material
    | other => throw (IO.userError s!"unknown credential provider `{other}`")
  store key live
  return live.secret

/-- Forget everything cached, so that the next request re-mints and asks again
where an App is installed.  What `kleis reload` does, and what a revoked
upstream token needs. -/
def Cache.clear (c : Cache) : IO Unit := do
  c.entries.set #[]
  c.missing.set #[]

end Credential
end Kleis
