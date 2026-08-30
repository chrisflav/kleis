import KleisTests.Harness

/-! # The decision

The scenarios the design promises, run end to end over the real manifest
loader, the real decoders and the real biscuit authorizer. -/

namespace KleisTests

open Kleis LeanBiscuit
open LeanBiscuit.Token (Biscuit BlockBuilder)

/-- The worked example from the design. -/
def manifestSource : String :=
"name  = \"github\"
hosts = [\"github.com\", \"api.github.com\", \"codeload.github.com\"]

datalog = '''
ref_update($ref) <-
  body($p, $ref), $p.length() == 3, $p.get(0) == \"updates\", $p.get(2) == \"ref\";
deletes_ref($ref) <-
  body($p, $ref), $p.length() == 3, $p.get(0) == \"updates\", $p.get(2) == \"ref\",
  body($q, true), $q.length() == 3, $q.get(0) == \"updates\",
  $q.get(1) == $p.get(1), $q.get(2) == \"delete\";
'''

[credential]
provider = \"static\"
hosts = [\"github.com\", \"api.github.com\", \"codeload.github.com\"]

[[credential.inject]]
kind = \"header\"
name = \"Authorization\"
template = \"Bearer {{secret}}\"

[[decoder]]
media = [\"application/x-git-receive-pack-request\"]
decoder = \"git-receive-pack\"

[[route]]
match = \"POST github.com /{owner}/{repo%.git}/git-receive-pack\"
emit  = ['operation(\"push\")', 'repository($owner, $repo)']

[[route]]
match = \"PUT api.github.com /repos/{owner}/{repo}/pulls/{number:int}/merge\"
emit  = ['operation(\"merge_pr\")', 'repository($owner, $repo)', 'pull_request($number)']

[[route]]
match = \"GET github.com /{owner}/{repo%.git}/info/refs\"
capture = { service = \"query:service\" }
emit  = ['operation(\"discover\")', 'repository($owner, $repo)',
         'discover_service($service)']
"

def grantSource : String :=
"name = \"ci-dev\"
service = \"github\"
credential = \"github/chrisflav\"
max_lifetime = \"24h\"
datalog = '''
// A push is two requests: the ref advertisement, then the pack.  Allowing only
// `operation(\"push\")` refuses the first and the push never starts.
allowed_operation(\"push\") <- operation(\"push\");
allowed_operation(\"discover\") <-
  operation(\"discover\"), discover_service(\"git-receive-pack\");

check if allowed_operation($x);
check if repository(\"chrisflav\", $r), [\"kleis\", \"lean-biscuit\"].contains($r);

// `reject if`, not `check all`: `check all` requires at least one match, so it
// would refuse the ref advertisement, which carries no ref updates at all.
reject if ref_update($ref), !$ref.starts_with(\"refs/heads/dev/\");
reject if deletes_ref($any);

allow if grant(\"ci-dev\");
'''
"

private def pkt (payload : String) : String :=
  let len := payload.utf8ByteSize + 4
  let hex := Str.toHex len
  String.ofList (List.replicate (4 - hex.length) '0') ++ hex ++ payload

private def zero : String := String.ofList (List.replicate 40 '0')
private def oidA : String := String.ofList (List.replicate 40 'a')
private def oidB : String := String.ofList (List.replicate 40 'b')

/-- A push body updating the given refs, followed by a packfile that must never
be looked at. -/
def pushBody (refs : List (String × String)) : Bytes :=
  let lines := refs.zipIdx.map fun ((old, ref), i) =>
    pkt (s!"{old} {oidB} {ref}" ++ (if i == 0 then "\x00report-status" else "") ++ "\n")
  Bytes.ofString (String.join lines ++ "0000PACK" ++ String.ofList (List.replicate 4000 'x'))

/-- A push that deletes refs.  A delete is a zero *new* id; a zero *old* id is
a create, and confusing the two is the easiest mistake to make here. -/
def deleteBody (refs : List String) : Bytes :=
  let lines := refs.zipIdx.map fun (ref, i) =>
    pkt (s!"{oidA} {zero} {ref}" ++ (if i == 0 then "\x00report-status" else "") ++ "\n")
  Bytes.ofString (String.join lines ++ "0000PACK")

/-- A key derived from a fixed seed, so the tests are reproducible. -/
def fixedKey (seed : UInt8) : PrivateKey :=
  match PrivateKey.ofBytes .ed25519 (Bytes.ofList (List.replicate 32 seed)) with
  | .ok k => k
  | .error _ => panic! "the fixed key is invalid"

/-- Issue a token for a grant, with optional attenuations. -/
def mkToken (grant bearer : String) (attenuations : List String := []) : Except String Biscuit := do
  let authority ← match BlockBuilder.code {}
      s!"grant(\"{grant}\"); bearer(\"{bearer}\");" with
    | .ok b => pure b
    | .error e => throw e.toString
  let token ← match Biscuit.create (fixedKey 7) (fixedKey 9) authority with
    | .ok t => pure t
    | .error e => throw e.toString
  attenuations.foldlM (init := token) fun t src =>
    Kleis.Token.attenuate t src (fixedKey 11)

/-- Decide one request against the worked example. -/
def decide (manifest : Service.Manifest) (grant : Policy.Grant) (token : Biscuit)
    (method host path : String) (body : Bytes) (contentType : Option String) :
    Policy.Outcome :=
  let headers : Http.Headers :=
    #[("host", host)] ++ (match contentType with
      | some c => #[("content-type", c)]
      | none => #[])
  let request : Model.Request := {
    method, scheme := "https", host, port := 443
    path := Str.pathOnly path
    segments := Str.pathSegments path
    query := Str.parseQuery path
    headers, bodyPrefix := body, bodyComplete := true
    bodySize := some body.size }
  let decoder := manifest.decoderFor contentType
  let decoded := match decoder with
    | .pure d => match d.step body true with
      | .done v _ => some v
      | _ => none
    | _ => none
  Policy.run {
    request
    body := Policy.Body.classify decoder.configured (body.size != 0) decoded
    manifest, grant, token, revoked := [], now := 1800000000
    clientIp := "127.0.0.1", requestId := "test" }

def policyTests : IO Unit := do
  group "manifest loading"
  let manifest ← match Service.Manifest.ofToml manifestSource with
    | .ok m => pure m
    | .error e => do check "the worked example loads" false e; return ()
  check "the worked example loads" true
  checkEq "hosts" manifest.hosts ["github.com", "api.github.com", "codeload.github.com"]
  checkEq "routes" manifest.routes.length 3
  checkEq "rules" manifest.rules.length 2

  -- The property that makes it safe to install a manifest you did not write.
  check "a manifest may not contain a policy"
    (Service.Manifest.ofToml (manifestSource ++ "\n[[unused]]\n")
      |>.toOption |>.isSome)
  let escalating := "name = \"x\"\nhosts = [\"x.com\"]\ndatalog = '''\nallow if true;\n'''\n"
  match Service.Manifest.ofToml escalating with
  | .error e => check "a manifest with a policy is refused" ((e.splitOn "policy").length > 1) e
  | .ok _ => check "a manifest with a policy is refused" false
  let checking := "name = \"x\"\nhosts = [\"x.com\"]\ndatalog = '''\ncheck if true;\n'''\n"
  match Service.Manifest.ofToml checking with
  | .error _ => check "a manifest with a check is refused" true
  | .ok _ => check "a manifest with a check is refused" false

  group "grant loading"
  let grant ← match Policy.Grant.ofToml grantSource with
    | .ok g => pure g
    | .error e => do check "the grant loads" false e; return ()
  check "the grant loads" true
  checkEq "max lifetime" grant.maxLifetime 86400
  match Policy.Grant.ofToml
      "name = \"x\"\nservice = \"y\"\ncredential = \"z\"\ndatalog = '''\ncheck if true;\n'''\n" with
  | .error _ => check "a grant with no policy is refused" true
  | .ok _ => check "a grant with no policy is refused" false

  group "decisions"
  let token ← match mkToken "ci-dev" "ci@build-07" with
    | .ok t => pure t
    | .error e => do check "a token can be issued" false e; return ()
  let push (refs : List (String × String)) :=
    decide manifest grant token "POST" "github.com"
      "/chrisflav/kleis.git/git-receive-pack" (pushBody refs)
      (some "application/x-git-receive-pack-request")

  check "a push to dev/ is allowed" (push [(oidA, "refs/heads/dev/feature")]).allowed
  check "a push to main is refused" (!(push [(oidA, "refs/heads/main")]).allowed)
  -- The classic hole: one good ref must not carry a bad one through.
  check "a mixed push is refused"
    (!(push [(oidA, "refs/heads/dev/a"), (oidA, "refs/heads/main")]).allowed)
  check "creating a dev ref is allowed" (push [(zero, "refs/heads/dev/new")]).allowed
  check "deleting a dev ref is refused"
    (!(decide manifest grant token "POST" "github.com"
        "/chrisflav/kleis.git/git-receive-pack" (deleteBody ["refs/heads/dev/old"])
        (some "application/x-git-receive-pack-request")).allowed)

  -- A refusal has to say why, or the bearer will just retry it.
  let denied := push [(oidA, "refs/heads/main")]
  match denied.decision with
  | .deny _ checks =>
    check "the failed check is named"
      (checks.any fun c => (c.splitOn "refs/heads/dev/").length > 1)
      (String.intercalate "; " checks)
  | .allow _ => check "the failed check is named" false

  -- The regression that a `check all` grant hides: a push is two requests, and
  -- the first one carries no ref updates at all.
  group "the ref advertisement"
  let discover (service repo : String) :=
    decide manifest grant token "GET" "github.com"
      s!"/chrisflav/{repo}.git/info/refs?service={service}" ByteArray.empty none
  check "discovery for a push is allowed" (discover "git-receive-pack" "kleis").allowed
  check "discovery for a fetch is not"
    (!(discover "git-upload-pack" "kleis").allowed)
  check "discovery for another repository is not"
    (!(discover "git-receive-pack" "secrets").allowed)

  group "more decisions"
  check "a push to another repository is refused"
    (!(decide manifest grant token "POST" "github.com"
        "/chrisflav/secrets.git/git-receive-pack"
        (pushBody [(oidA, "refs/heads/dev/x")])
        (some "application/x-git-receive-pack-request")).allowed)
  check "a merge is refused by a push-only grant"
    (!(decide manifest grant token "PUT" "api.github.com"
        "/repos/chrisflav/kleis/pulls/7/merge" (Bytes.ofString "{}")
        (some "application/json")).allowed)

  group "a body nobody could read"
  -- The trap `reject if` sets: it is vacuously satisfied when the facts it
  -- rejects on are absent, and a body the decoder choked on has no facts at
  -- all.  The authorizer refuses on `body_undecodable`, so the grant does not
  -- have to remember.
  let unreadable := decide manifest grant token "POST" "github.com"
    "/chrisflav/kleis.git/git-receive-pack" (Bytes.ofString "not pkt-lines")
    (some "application/x-git-receive-pack-request")
  check "a push the configured decoder could not read is refused" (!unreadable.allowed)
  check "and it is refused for being unreadable, not for its refs"
    (unreadable.facts.contains "body_undecodable(true)")
    (String.intercalate " " (unreadable.facts.filter fun f => f.startsWith "body_"))
  -- A body no decoder was configured for is a different thing, and is not
  -- refused on those grounds: plenty of services have bodies no policy cares
  -- about.
  let uninspected := decide manifest grant token "POST" "github.com"
    "/chrisflav/kleis.git/git-receive-pack" (Bytes.ofString "whatever")
    (some "application/octet-stream")
  check "a body nobody was asked to read is not undecodable"
    (uninspected.facts.contains "body_undecodable(false)")
  check "though it is opaque" (uninspected.facts.contains "body_opaque(true)")

  group "attenuation is monotone"
  let narrowed ← match mkToken "ci-dev" "ci@build-07"
      ["check if repository(\"chrisflav\", \"lean-biscuit\");"] with
    | .ok t => pure t
    | .error e => do check "a token can be attenuated" false e; return ()
  check "a token can be attenuated" true
  let pushWith (t : Biscuit) (repo ref : String) :=
    decide manifest grant t "POST" "github.com"
      s!"/chrisflav/{repo}.git/git-receive-pack"
      (pushBody [(oidA, ref)]) (some "application/x-git-receive-pack-request")
  check "the parent may push to kleis" (pushWith token "kleis" "refs/heads/dev/x").allowed
  check "the attenuation may not" (!(pushWith narrowed "kleis" "refs/heads/dev/x").allowed)
  check "the attenuation may still push to what it kept"
    (pushWith narrowed "lean-biscuit" "refs/heads/dev/x").allowed
  check "and cannot regain what the parent refused"
    (!(pushWith narrowed "lean-biscuit" "refs/heads/main").allowed)
  -- An attenuation may only narrow: adding a fact would be gaining authority.
  match Kleis.Token.attenuate token "repository(\"chrisflav\", \"anything\");" (fixedKey 11) with
  | .error _ => check "an attenuation may not add a fact" true
  | .ok _ => check "an attenuation may not add a fact" false

  group "a token for another grant"
  let other ← match mkToken "other" "x" with
    | .ok t => pure t
    | .error _ => do check "a second token can be issued" false; return ()
  check "a token naming a different grant does not match this one's allow"
    (!(decide manifest grant other "POST" "github.com"
        "/chrisflav/kleis.git/git-receive-pack"
        (pushBody [(oidA, "refs/heads/dev/x")])
        (some "application/x-git-receive-pack-request")).allowed)

  group "revocation"
  let revoked := Policy.run {
    request := {
      method := "POST", scheme := "https", host := "github.com", port := 443
      path := "/chrisflav/kleis.git/git-receive-pack"
      segments := #["chrisflav", "kleis.git", "git-receive-pack"]
      query := #[], headers := #[("host", "github.com")]
      bodyPrefix := ByteArray.empty, bodyComplete := true, bodySize := none }
    body := .absent, manifest, grant, token
    revoked := (Biscuit.revocationIdentifiers token).map Bytes.toHex
    now := 1800000000, clientIp := "127.0.0.1", requestId := "test" }
  check "a revoked token is refused" (!revoked.allowed)
  match revoked.decision with
  | .deny r _ => check "and says so" ((r.splitOn "revoked").length > 1) r
  | _ => check "and says so" false

end KleisTests
