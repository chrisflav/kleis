import KleisTests.Policy

/-! # Several grants, issuers, GraphQL, and the orchestra example

The shipped GitHub manifest and the grants in `examples/orchestra/`, decided
against the requests an agent's `git` and `gh` actually make. -/

namespace KleisTests

open Kleis LeanBiscuit
open LeanBiscuit.Token (Biscuit BlockBuilder)

/-- Read a file the tests ship with, relative to the package root. -/
private def example? (path : String) : IO String := IO.FS.readFile path

/-- Issue a token the way the daemon does for an issuer. -/
private def orchestraToken (grants : List String) (facts : List String)
    (issuedBy : Option String := some "orchestra") : Except String Biscuit := do
  let facts ← facts.mapM Token.factOfSource
  let (t, _) ← Token.issue (fixedKey 7)
    { grants, bearer := "orchestra:test", lifetime := 3600, issuedBy, extraFacts := facts }
    1700000000 (fixedKey 9)
  pure t

/-- Decide one request the way the proxy does: the manifest's decoder for the
request, then each of the token's grants in turn. -/
def choose (registry : Service.Registry) (token : Biscuit) (method host path : String)
    (body : String := "") (contentType : Option String := none) :
    Except String Policy.Choice := do
  let bytes := Bytes.ofString body
  let headers : Http.Headers :=
    #[("host", host)] ++ (match contentType with
      | some c => #[("content-type", c)]
      | none => #[])
  let request : Model.Request := {
    method, scheme := "https", host, port := 443
    path := Str.pathOnly path
    segments := Str.pathSegments path
    query := Str.parseQuery path
    headers, bodyPrefix := bytes, bodyComplete := true
    bodySize := some bytes.size }
  let some manifest := registry.forHost? host | throw s!"no manifest for {host}"
  let grants ← match Policy.candidates registry token manifest host with
    | .ok gs => pure gs
    | .error r => throw r.toString
  let decoder := manifest.decoderFor contentType request
  let decoded := match decoder with
    | .pure d => match d.step bytes true with
      | .done v _ => some v
      | _ => none
    | _ => none
  pure <| Policy.choose grants fun grant => {
    request
    body := Policy.Body.classify decoder.configured (bytes.size != 0) decoded
    manifest, grant, token, revoked := [], now := 1700000100
    clientIp := "127.0.0.1", requestId := "test" }

/-- Which grant allowed a request, or `none` if none did. -/
def allowedBy (c : Except String Policy.Choice) : Option String :=
  match c with
  | .ok c => if c.outcome.allowed then some c.grant.name else none
  | .error _ => none

def orchestraTests : IO Unit := do
  group "graphql documents"
  let ops (d : String) := (Wire.GraphQL.operations d).map (·.map fun o => (o.kind, o.name))
  checkEq "a named query" (ops "query Viewer { viewer { login } }") (some [("query", "Viewer")])
  checkEq "the shorthand is a query" (ops "{ viewer { login } }") (some [("query", "")])
  checkEq "a mutation with variables and a default"
    (ops "mutation M($x: Int = 3, $o: In = {a: [1]}) { b(x: $x) { id } }")
    (some [("mutation", "M")])
  checkEq "every operation in a document"
    (ops "query A { a } mutation B { b }") (some [("query", "A"), ("mutation", "B")])
  checkEq "a fragment is not an operation"
    (ops "query A { ...F } fragment F on Repository { name }") (some [("query", "A")])
  checkEq "braces in strings and comments are not structure"
    (ops "# mutation {\nquery Q { a(s: \"}{\", t: \"\"\" } \"\"\") }")
    (some [("query", "Q")])
  checkEq "something that is not a document" (ops "mutation") none
  checkEq "an unbalanced document" (ops "query { a ") none

  group "facts an issuer may state"
  let isSet : Builder.Term → Bool := fun t => match t with
    | .set _ => true
    | _ => false
  let labels := Token.factOfJson (Json.obj [("name", .str "task_pr_labels"),
      ("terms", .arr [.arr [.str "b", .str "a"]])])
  check "an array becomes a set"
    (match labels with
     | .ok f => f.predicate.terms.length == 1 && f.predicate.terms.all isSet
     | .error _ => false)
  check "an object is refused"
    (Token.factOfJson (Json.obj [("name", .str "task_x"), ("terms", .arr [.obj []])])).toOption.isNone
  check "a predicate name with punctuation is refused"
    (Token.factOfJson (Json.obj [("name", .str "x\"); y(\""), ("terms", .arr [])])).toOption.isNone
  check "a reserved fact cannot be issued"
    (orchestraToken ["orchestra-fork"] ["repository(\"a\", \"b\")"]).toOption.isNone
  check "nor a request fact"
    (orchestraToken ["orchestra-fork"] ["request_host(\"github.com\")"]).toOption.isNone

  group "issuers"
  let configText ← example? "examples/orchestra/config.toml"
  match Config.ofToml configText with
  | .error e => check "the example configuration loads" false e
  | .ok config =>
    check "the example configuration loads" true
    match config.issuer? "orchestra" with
    | none => check "it has the orchestra issuer" false
    | some i =>
      check "the issuer may claim its grants" (i.mayClaim "orchestra-fork")
      check "and no others" (!i.mayClaim "admin")
      check "it may state task facts" (i.mayState "task_fork")
      check "and no others" (!i.mayState "operation")
      checkEq "its tokens live a day at most" i.maxTtl 86400
    check "every host passes" (config.passes "api.anthropic.com")
  check "an issuer may not be allowed every fact"
    (Config.ofToml "[[issuer]]\nname = \"x\"\nfacts = [\"*\"]\n").toOption.isNone

  group "the orchestra grants"
  let manifest ← match Service.Manifest.ofToml (← example? "examples/github.toml") with
    | .ok m => pure m
    | .error e => do check "the GitHub manifest loads" false e; return ()
  check "the GitHub manifest loads" true
  let mut grants : Array Policy.Grant := #[]
  for name in ["orchestra-fork", "orchestra-upstream", "orchestra-triage", "orchestra-public"] do
    match Policy.Grant.ofToml (← example? s!"examples/orchestra/grants/{name}.toml") with
    | .ok g => grants := grants.push g
    | .error e => check s!"{name} loads" false e
  checkEq "every grant loads" grants.size 4
  check "the public grant is anonymous"
    ((grants.find? (·.name == "orchestra-public")).bind (·.credential) |>.isNone)
  let registry : Service.Registry := { manifests := #[manifest], grants }
  let order := ["orchestra-fork", "orchestra-upstream", "orchestra-triage", "orchestra-public"]
  let base := ["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")",
    "task_issue(7)", "task_writable(true)", "task_pr_labels([\"orchestra\"])"]
  let token ← match orchestraToken order
      (base ++ ["task_tool(\"create_pr\")", "task_tool(\"comment\")"]) with
    | .ok t => pure t
    | .error e => do check "a job's token can be issued" false e; return ()
  let push (repo ref : String) (old := String.ofList (List.replicate 40 'a'))
      (t := token) :=
    allowedBy (choose registry t "POST" "github.com" s!"/{repo}.git/git-receive-pack"
      (Bytes.toStringLossy (pushBody [(old, ref)]))
      (some "application/x-git-receive-pack-request"))

  checkEq "a push to the fork goes out on the App's token"
    (push "bot/proj" "refs/heads/feature") (some "orchestra-fork")
  checkEq "a push to the upstream is refused" (push "up/proj" "refs/heads/feature") none
  checkEq "a push anywhere else is refused" (push "bot/other" "refs/heads/feature") none
  checkEq "the ref advertisement for a push to the fork"
    (allowedBy (choose registry token "GET" "github.com"
      "/bot/proj.git/info/refs?service=git-receive-pack")) (some "orchestra-fork")
  checkEq "a fetch of the fork uses the App's token"
    (allowedBy (choose registry token "GET" "github.com"
      "/bot/proj.git/info/refs?service=git-upload-pack")) (some "orchestra-fork")
  checkEq "a fetch of the upstream uses the person's token"
    (allowedBy (choose registry token "GET" "github.com"
      "/up/proj.git/info/refs?service=git-upload-pack")) (some "orchestra-upstream")
  checkEq "a fetch of anything else uses no token"
    (allowedBy (choose registry token "GET" "github.com"
      "/leanprover-community/mathlib4.git/info/refs?service=git-upload-pack"))
    (some "orchestra-public")
  checkEq "a push there is refused by every grant"
    (push "leanprover-community/mathlib4" "refs/heads/master") none
  match choose registry token "POST" "github.com" "/up/proj.git/git-receive-pack"
      (Bytes.toStringLossy (pushBody [(String.ofList (List.replicate 40 'a'), "refs/heads/x")]))
      (some "application/x-git-receive-pack-request") with
  | .ok c =>
    check "a refusal names every grant it tried" ((c.reason.splitOn "grant `").length == 5) c.reason
  | .error e => check "a refusal names every grant it tried" false e

  let readOnly ← match orchestraToken order
      ["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")"] with
    | .ok t => pure t
    | .error e => do check "a read-only token can be issued" false e; return ()
  checkEq "a read-only job cannot push" (push "bot/proj" "refs/heads/x" (t := readOnly)) none
  checkEq "nor start one"
    (allowedBy (choose registry readOnly "GET" "github.com"
      "/bot/proj.git/info/refs?service=git-receive-pack")) none

  let prefixed ← match orchestraToken order
      (base ++ ["task_push_prefix(\"refs/heads/orchestra/\")"]) with
    | .ok t => pure t
    | .error e => do check "a token with a push prefix can be issued" false e; return ()
  checkEq "a push under the prefix"
    (push "bot/proj" "refs/heads/orchestra/x" (t := prefixed)) (some "orchestra-fork")
  checkEq "a push outside it" (push "bot/proj" "refs/heads/main" (t := prefixed)) none

  let api (method path : String) (body : String := "") (t := token) :=
    allowedBy (choose registry t method "api.github.com" path body
      (if body.isEmpty then none else some "application/json"))
  checkEq "a pull request from the fork to the upstream"
    (api "POST" "/repos/up/proj/pulls" "{\"head\":\"bot:feature\",\"base\":\"main\",\"title\":\"t\"}")
    (some "orchestra-upstream")
  checkEq "not from somebody else's fork"
    (api "POST" "/repos/up/proj/pulls" "{\"head\":\"evil:feature\",\"base\":\"main\"}") none
  checkEq "a pull request on the fork"
    (api "POST" "/repos/bot/proj/pulls" "{\"head\":\"feature\",\"base\":\"main\"}")
    (some "orchestra-fork")
  checkEq "a comment on the job's own issue"
    (api "POST" "/repos/up/proj/issues/7/comments" "{\"body\":\"hi\"}") (some "orchestra-upstream")
  checkEq "not on another"
    (api "POST" "/repos/up/proj/issues/8/comments" "{\"body\":\"hi\"}") none
  checkEq "a review that comments"
    (api "POST" "/repos/up/proj/pulls/7/reviews" "{\"event\":\"COMMENT\",\"body\":\"x\"}")
    (some "orchestra-upstream")
  checkEq "not one that approves"
    (api "POST" "/repos/up/proj/pulls/7/reviews" "{\"event\":\"APPROVE\"}") none
  checkEq "a reply to an inline comment"
    (api "POST" "/repos/up/proj/pulls/7/comments/99/replies" "{\"body\":\"x\"}")
    (some "orchestra-upstream")
  checkEq "a merge without merge_pr" (api "PUT" "/repos/up/proj/pulls/7/merge" "{}") none
  checkEq "the job's pull request labels"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"orchestra\"]}")
    (some "orchestra-upstream")
  checkEq "and no others"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"orchestra\",\"p-high\"]}") none
  checkEq "creating the job's label"
    (api "POST" "/repos/up/proj/labels" "{\"name\":\"orchestra\",\"color\":\"ffffff\"}")
    (some "orchestra-upstream")
  checkEq "not another" (api "POST" "/repos/up/proj/labels" "{\"name\":\"x\"}") none
  checkEq "editing an issue is nobody's" (api "PATCH" "/repos/up/proj/issues/7" "{\"state\":\"closed\"}") none

  let triage ← match orchestraToken order (base ++ ["task_tool(\"label_issue\")"]) with
    | .ok t => pure t
    | .error e => do check "a triage token can be issued" false e; return ()
  checkEq "with label_issue any label on any issue"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"p-high\"]}" (t := triage))
    (some "orchestra-triage")
  checkEq "and removing one"
    (api "DELETE" "/repos/up/proj/issues/12/labels/p-high" (t := triage)) (some "orchestra-triage")
  checkEq "but on the upstream only"
    (api "POST" "/repos/other/proj/issues/12/labels" "{\"labels\":[\"x\"]}" (t := triage)) none

  let merger ← match orchestraToken order (base ++ ["task_tool(\"merge_pr\")"]) with
    | .ok t => pure t
    | .error e => do check "a merging token can be issued" false e; return ()
  checkEq "a merge with merge_pr"
    (api "PUT" "/repos/up/proj/pulls/3/merge" "{\"merge_method\":\"squash\"}" (t := merger))
    (some "orchestra-upstream")

  checkEq "a GraphQL query"
    (api "POST" "/graphql" "{\"query\":\"query { viewer { login } }\"}") (some "orchestra-fork")
  checkEq "a GraphQL mutation"
    (api "POST" "/graphql" "{\"query\":\"mutation { addComment(input: {}) { clientMutationId } }\"}")
    none
  checkEq "a mutation behind a query"
    (api "POST" "/graphql" "{\"query\":\"query A { a } mutation B { b }\",\"operationName\":\"A\"}")
    none
  checkEq "a document nobody can read"
    (api "POST" "/graphql" "{\"query\":\"mutation\"}") none
  checkEq "a client's own `$operations` is replaced"
    (api "POST" "/graphql"
      "{\"query\":\"mutation { x }\",\"$operations\":[{\"type\":\"query\",\"name\":\"\"}]}") none
  checkEq "reading the upstream through the API"
    (api "GET" "/repos/up/proj/pulls/7/comments") (some "orchestra-upstream")
  checkEq "reading anything else anonymously"
    (api "GET" "/repos/torvalds/linux") (some "orchestra-public")
  checkEq "and reads about no repository" (api "GET" "/rate_limit") (some "orchestra-public")
  checkEq "an endpoint no route knows" (api "POST" "/user/repos" "{\"name\":\"x\"}") none

  let foreign ← match orchestraToken order base (issuedBy := none) with
    | .ok t => pure t
    | .error e => do check "a token from elsewhere can be issued" false e; return ()
  checkEq "a token orchestra did not issue reaches nothing"
    (allowedBy (choose registry foreign "GET" "github.com"
      "/leanprover-community/mathlib4.git/info/refs?service=git-upload-pack")) none

  group "attenuation applies to every grant"
  let attenuation := "check if operation(\"fetch\") or operation(\"discover\");"
  let narrowed ← match orchestraToken order (base ++ ["task_tool(\"comment\")"]) |>.bind
      (Token.attenuate · attenuation (fixedKey 11)) with
    | .ok n => pure n
    | .error e => do check "a job's token can be attenuated" false e; return ()
  checkEq "a narrowed token may still fetch"
    (allowedBy (choose registry narrowed "GET" "github.com"
      "/up/proj.git/info/refs?service=git-upload-pack")) (some "orchestra-upstream")
  checkEq "and may not comment"
    (api "POST" "/repos/up/proj/issues/7/comments" "{\"body\":\"hi\"}" (t := narrowed)) none

end KleisTests
