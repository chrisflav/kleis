import KleisTests.Policy

/-! # The properties that are the point

Each of these corresponds to a claim in `DESIGN.md`, and each of them is a
thing that would be a vulnerability rather than a bug. -/

namespace KleisTests

open Kleis LeanBiscuit

def securityTests : IO Unit := do
  group "captures cannot be read as datalog"
  -- A repository name that closes the predicate and opens another.  If the
  -- emitted fact were built by pasting text and re-parsing, this would let a
  -- URL write its own authority.
  let hostile := "a\") or admin(\"x"
  let manifest ← match Service.Manifest.ofToml manifestSource with
    | .ok m => pure m
    | .error e => do check "manifest" false e; return ()
  let grant ← match Policy.Grant.ofToml grantSource with
    | .ok g => pure g
    | .error e => do check "grant" false e; return ()
  let token ← match mkToken "ci-dev" "ci" with
    | .ok t => pure t
    | .error e => do check "token" false e; return ()
  let outcome := decide manifest grant token "POST" "github.com"
    s!"/chrisflav/{Str.percentEncode hostile}.git/git-receive-pack"
    (pushBody [(String.ofList (List.replicate 40 'a'), "refs/heads/dev/x")])
    (some "application/x-git-receive-pack-request")
  check "an injection attempt is simply refused" (!outcome.allowed)
  -- The hostile text does appear — inside a quoted string term, which is
  -- exactly the point.  What must not exist is a *predicate* called `admin`.
  check "and no `admin` predicate was ever created"
    (!outcome.facts.any fun f => f.startsWith "admin(")
    (String.intercalate " | " (outcome.facts.filter fun f => (f.splitOn "admin").length > 1))
  -- The name does reach datalog, as a string, which is the point: it is data.
  check "the hostile name is present as a string term"
    (outcome.facts.any fun f => (f.splitOn "repository(").length > 1)

  group "the credential is confined to its bound hosts"
  let secret := Credential.Secret.ofString "s3cret-token"
  -- `bind` needs an AuthorizedRequest, which only the authorizer makes, so
  -- reaching this at all required a decision.
  let allowedOutcome := decide manifest grant token "POST" "github.com"
    "/chrisflav/kleis.git/git-receive-pack"
    (pushBody [(String.ofList (List.replicate 40 'a'), "refs/heads/dev/x")])
    (some "application/x-git-receive-pack-request")
  match allowedOutcome.authorized with
  | none => check "the allowed request produced an authorization" false
  | some authorized => do
    check "the allowed request produced an authorization" true
    match Credential.bind authorized secret with
    | .error e => check "binding to a bound host succeeds" false e.toString
    | .ok out => do
      check "binding to a bound host succeeds" true
      checkEq "the credential is in the header"
        (Http.Headers.find? out.headers "authorization") (some "Bearer s3cret-token")
      check "a client-supplied Authorization was removed first"
        ((Http.Headers.findAll out.headers "authorization").size == 1)

  -- A manifest whose credential is bound to fewer hosts than it claims.
  let narrowManifest := manifestSource.replace
    "hosts = [\"github.com\", \"api.github.com\", \"codeload.github.com\"]\n\n[[credential.inject]]"
    "hosts = [\"api.github.com\"]\n\n[[credential.inject]]"
  match Service.Manifest.ofToml narrowManifest with
  | .error e => check "a narrowly bound manifest loads" false e
  | .ok m =>
    check "a narrowly bound manifest loads" true
    check "github.com is claimed" (m.claims "github.com")
    check "but the credential may not go there" (!m.mayCredentialReach "github.com")
    check "while api.github.com may" (m.mayCredentialReach "api.github.com")
    let outcome := decide m grant token "POST" "github.com"
      "/chrisflav/kleis.git/git-receive-pack"
      (pushBody [(String.ofList (List.replicate 40 'a'), "refs/heads/dev/x")])
      (some "application/x-git-receive-pack-request")
    match outcome.authorized with
    | none => check "the request is still authorized" false
    | some authorized =>
      check "the request is still authorized" true
      match Credential.bind authorized secret with
      | .ok _ => check "but the credential cannot be attached to it" false
      | .error e =>
        check "but the credential cannot be attached to it" true
        check "and says which host" ((e.toString.splitOn "github.com").length > 1) e.toString
      let stripped := Credential.stripOnly authorized
      check "the request may still be forwarded, without a credential"
        (!Http.Headers.contains stripped.headers "authorization")

  -- A manifest may not bind its credential to a host it does not claim: that
  -- would be a credential leaving for somewhere nothing routes.
  let overreaching := "name = \"x\"\nhosts = [\"a.com\"]\n\n[credential]\nhosts = [\"b.com\"]\n"
  match Service.Manifest.ofToml overreaching with
  | .error _ => check "a credential cannot be bound outside the manifest's hosts" true
  | .ok _ => check "a credential cannot be bound outside the manifest's hosts" false

  group "injection can differ per host"
  -- Only the real service tells you this: GitHub's git endpoints want HTTP
  -- basic authentication and its REST API wants `Authorization: Bearer`, so
  -- one injection for the whole service sends the wrong scheme to one of them
  -- and gets `invalid credentials` back, which says nothing about why.
  let twoSchemes := "name = \"gh\"\nhosts = [\"github.com\", \"api.github.com\"]\n\n\
    [credential]\nprovider = \"static\"\n\n\
    [[credential.inject]]\nhosts = [\"github.com\"]\nkind = \"basic\"\n\
    template = \"x-access-token:{{secret}}\"\n\n\
    [[credential.inject]]\nhosts = [\"api.github.com\"]\nkind = \"header\"\n\
    name = \"Authorization\"\ntemplate = \"Bearer {{secret}}\"\n"
  match Service.Manifest.ofToml twoSchemes with
  | .error e => check "a manifest with per-host injection loads" false e
  | .ok m => do
    check "a manifest with per-host injection loads" true
    checkEq "two injections" m.credential.inject.length 2
    let gitOnly := m.credential.inject.filter (·.appliesTo "github.com")
    let apiOnly := m.credential.inject.filter (·.appliesTo "api.github.com")
    checkEq "one applies to the git host" gitOnly.length 1
    checkEq "one applies to the API host" apiOnly.length 1
    check "and they are not the same one"
      ((gitOnly.head!).kind != (apiOnly.head!).kind)
    -- An injection with no hosts applies everywhere, which is the common case.
    match Service.Manifest.ofToml
        ("name = \"x\"\nhosts = [\"a.com\", \"b.com\"]\n\n[credential]\n\n\
          [[credential.inject]]\nkind = \"header\"\nname = \"X\"\ntemplate = \"t\"\n") with
    | .error e => check "an unrestricted injection loads" false e
    | .ok m2 => do
      check "an unrestricted injection loads" true
      check "and applies to every host"
        ((m2.credential.inject.head!).appliesTo "a.com" &&
         (m2.credential.inject.head!).appliesTo "b.com")

  group "a secret does not leak into anything printable"
  checkEq "the fingerprint is not the secret"
    (secret.fingerprint == "s3cret-token") false
  checkEq "the fingerprint is stable" secret.fingerprint
    (Credential.Secret.ofString "s3cret-token").fingerprint
  checkEq "different secrets fingerprint differently"
    (secret.fingerprint == (Credential.Secret.ofString "other").fingerprint) false

  group "the body truncation guard"
  -- A manifest that will not flatten more than a couple of facts, so an
  -- ordinary push overflows it.  The setting goes at the *top*: in TOML a key
  -- after a `[[route]]` header belongs to that table, not to the document.
  let tiny := "max_body_facts = 2\n" ++ manifestSource
  match Service.Manifest.ofToml tiny with
  | .error e => check "a capped manifest loads" false e
  | .ok m =>
    check "a capped manifest loads" true
    checkEq "the cap took" m.maxBodyFacts 2
    let outcome := decide m grant token "POST" "github.com"
      "/chrisflav/kleis.git/git-receive-pack"
      (pushBody [(String.ofList (List.replicate 40 'a'), "refs/heads/dev/x")])
      (some "application/x-git-receive-pack-request")
    check "a body too large to reason about is refused, not ignored" (!outcome.allowed)

  group "host wildcards"
  check "an exact host matches" (Facts.hostMatches "github.com" "github.com")
  check "a wildcard matches a subdomain" (Facts.hostMatches "*.github.com" "api.github.com")
  -- A wildcard that silently included the apex would be a surprise in the
  -- wrong direction.
  check "a wildcard does not match the apex" (!Facts.hostMatches "*.github.com" "github.com")
  check "a wildcard does not match a suffix of another name"
    (!Facts.hostMatches "*.github.com" "evilgithub.com")

end KleisTests
