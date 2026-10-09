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
    (body : String := "") (contentType : Option String := none)
    (remembered : List Builder.Fact := []) :
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
    clientIp := "127.0.0.1", requestId := "test", remembered }

/-- Which grant allowed a request, or `none` if none did. -/
def allowedBy (c : Except String Policy.Choice) : Option String :=
  match c with
  | .ok c => if c.outcome.allowed then some c.grant.name else none
  | .error _ => none

/-- What a request went out on: `none` if it was refused, `some "-"` if it was
allowed with no credential, and `some name` for a credential. -/
def spentOn (c : Except String Policy.Choice) : Option String :=
  match c with
  | .ok c => c.outcome.authorized.map fun a => a.credential.getD "-"
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

  group "the orchestra grant"
  let manifest ← match Service.Manifest.ofToml (← example? "examples/github.toml") with
    | .ok m => pure m
    | .error e => do check "the GitHub manifest loads" false e; return ()
  check "the GitHub manifest loads" true
  let grant ← match Policy.Grant.ofToml (← example? "examples/orchestra/grants/orchestra-github.toml") with
    | .ok g => pure g
    | .error e => do check "the orchestra grant loads" false e; return ()
  check "the orchestra grant loads" true
  checkEq "it may spend both credentials" grant.spendable
    ["github/orchestra-app", "github/orchestra-pat"]
  let registry : Service.Registry := { manifests := #[manifest], grants := #[grant] }
  let base := ["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")",
    "task_issue(7)", "task_writable(true)", "task_pr_labels([\"orchestra\"])",
    "task_label_any(false)"]
  let token ← match orchestraToken ["orchestra-github"]
      (base ++ ["task_tool(\"create_pr\")", "task_tool(\"comment\")"]) with
    | .ok t => pure t
    | .error e => do check "a job's token can be issued" false e; return ()
  let oid := String.ofList (List.replicate 40 'a')
  let push (repo ref : String) (t := token) (remembered : List Builder.Fact := []) :=
    spentOn (choose registry t "POST" "github.com" s!"/{repo}.git/git-receive-pack"
      (Bytes.toStringLossy (pushBody [(oid, ref)]))
      (some "application/x-git-receive-pack-request") remembered)
  let git (path : String) (t := token) := spentOn (choose registry t "GET" "github.com" path)
  let api (method path : String) (body : String := "") (t := token)
      (remembered : List Builder.Fact := []) :=
    spentOn (choose registry t method "api.github.com" path body
      (if body.isEmpty then none else some "application/json") remembered)
  let app := some "github/orchestra-app"
  let pat := some "github/orchestra-pat"
  let anonymous := some "-"

  checkEq "a push to the fork goes out on the App's token"
    (push "bot/proj" "refs/heads/feature") app
  checkEq "a push to the upstream is refused" (push "up/proj" "refs/heads/feature") none
  checkEq "a push anywhere else is refused" (push "bot/other" "refs/heads/feature") none
  checkEq "deleting a branch is refused"
    (spentOn (choose registry token "POST" "github.com" "/bot/proj.git/git-receive-pack"
      (Bytes.toStringLossy (deleteBody ["refs/heads/x"]))
      (some "application/x-git-receive-pack-request"))) none
  checkEq "the ref advertisement for a push to the fork"
    (git "/bot/proj.git/info/refs?service=git-receive-pack") app
  checkEq "a fetch of the fork uses the App's token"
    (git "/bot/proj.git/info/refs?service=git-upload-pack") app
  checkEq "a fetch of the upstream uses the operator's token"
    (git "/up/proj.git/info/refs?service=git-upload-pack") pat
  checkEq "a fetch of anything else uses no token"
    (git "/leanprover-community/mathlib4.git/info/refs?service=git-upload-pack") anonymous
  checkEq "a push there is refused" (push "leanprover-community/mathlib4" "refs/heads/master") none

  let readOnly ← match orchestraToken ["orchestra-github"]
      ["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")"] with
    | .ok t => pure t
    | .error e => do check "a read-only token can be issued" false e; return ()
  checkEq "a read-only job cannot push" (push "bot/proj" "refs/heads/x" (t := readOnly)) none
  checkEq "nor start one" (git "/bot/proj.git/info/refs?service=git-receive-pack" (t := readOnly)) none

  let prefixed ← match orchestraToken ["orchestra-github"]
      (base ++ ["task_push_prefix(\"refs/heads/orchestra/\")"]) with
    | .ok t => pure t
    | .error e => do check "a token with a push prefix can be issued" false e; return ()
  checkEq "a push under the prefix" (push "bot/proj" "refs/heads/orchestra/x" (t := prefixed)) app
  checkEq "a push outside it" (push "bot/proj" "refs/heads/main" (t := prefixed)) none

  checkEq "a pull request from the fork to the upstream, on the operator's token"
    (api "POST" "/repos/up/proj/pulls" "{\"head\":\"bot:feature\",\"base\":\"main\",\"title\":\"t\"}") pat
  checkEq "not from somebody else's fork"
    (api "POST" "/repos/up/proj/pulls" "{\"head\":\"evil:feature\",\"base\":\"main\"}") none
  checkEq "a pull request on the fork, on the App's"
    (api "POST" "/repos/bot/proj/pulls" "{\"head\":\"feature\",\"base\":\"main\"}") app
  checkEq "a comment on the job's own issue"
    (api "POST" "/repos/up/proj/issues/7/comments" "{\"body\":\"hi\"}") pat
  checkEq "not on another" (api "POST" "/repos/up/proj/issues/8/comments" "{\"body\":\"hi\"}") none
  checkEq "a review that comments"
    (api "POST" "/repos/up/proj/pulls/7/reviews" "{\"event\":\"COMMENT\",\"body\":\"x\"}") pat
  checkEq "not one that approves"
    (api "POST" "/repos/up/proj/pulls/7/reviews" "{\"event\":\"APPROVE\"}") none
  checkEq "a reply to an inline comment"
    (api "POST" "/repos/up/proj/pulls/7/comments/99/replies" "{\"body\":\"x\"}") pat
  checkEq "a merge without merge_pr" (api "PUT" "/repos/up/proj/pulls/7/merge" "{}") none
  checkEq "the job's pull request labels"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"orchestra\"]}") pat
  checkEq "and no others"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"orchestra\",\"p-high\"]}") none
  checkEq "creating the job's label"
    (api "POST" "/repos/up/proj/labels" "{\"name\":\"orchestra\",\"color\":\"ffffff\"}") pat
  checkEq "not another" (api "POST" "/repos/up/proj/labels" "{\"name\":\"x\"}") none
  checkEq "editing an issue is nobody's"
    (api "PATCH" "/repos/up/proj/issues/7" "{\"state\":\"closed\"}") none

  let unlabelled ← match orchestraToken ["orchestra-github"]
      (["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")",
        "task_tool(\"create_pr\")"]) with
    | .ok t => pure t
    | .error e => do check "a token without label facts can be issued" false e; return ()
  checkEq "without the label facts no label is allowed at all"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"anything\"]}" (t := unlabelled)) none

  let triage ← match orchestraToken ["orchestra-github"]
      (["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")",
        "task_pr_labels([])", "task_label_any(true)", "task_tool(\"label_issue\")"]) with
    | .ok t => pure t
    | .error e => do check "a triage token can be issued" false e; return ()
  checkEq "with label_issue any label on any issue"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[\"p-high\"]}" (t := triage)) pat
  checkEq "and removing one" (api "DELETE" "/repos/up/proj/issues/12/labels/p-high" (t := triage)) pat
  checkEq "but on the upstream only"
    (api "POST" "/repos/other/proj/issues/12/labels" "{\"labels\":[\"x\"]}" (t := triage)) none

  let merger ← match orchestraToken ["orchestra-github"] (base ++ ["task_tool(\"merge_pr\")"]) with
    | .ok t => pure t
    | .error e => do check "a merging token can be issued" false e; return ()
  checkEq "a merge with merge_pr"
    (api "PUT" "/repos/up/proj/pulls/3/merge" "{\"merge_method\":\"squash\"}" (t := merger)) pat

  checkEq "a GraphQL query, on the App's token"
    (api "POST" "/graphql" "{\"query\":\"query { viewer { login } }\"}") app
  checkEq "a GraphQL mutation"
    (api "POST" "/graphql" "{\"query\":\"mutation { addComment(input: {}) { clientMutationId } }\"}") none
  checkEq "a mutation behind a query"
    (api "POST" "/graphql" "{\"query\":\"query A { a } mutation B { b }\",\"operationName\":\"A\"}") none
  checkEq "a document nobody can read" (api "POST" "/graphql" "{\"query\":\"mutation\"}") none
  checkEq "reading the upstream through the API" (api "GET" "/repos/up/proj/pulls/7/comments") pat
  checkEq "reading anything else anonymously" (api "GET" "/repos/torvalds/linux") anonymous
  checkEq "and reads about no repository" (api "GET" "/rate_limit") anonymous
  checkEq "an endpoint no route knows" (api "POST" "/user/repos" "{\"name\":\"x\"}") none


  group "what the reviews found"
  let wireOf (target : String) : Http.Request :=
    { method := "GET", target, version := "HTTP/1.1", headers := #[("host", "api.github.com")]
      framing := .empty }
  let parsed (target : String) := Model.Request.ofWire (wireOf target) "https" none ByteArray.empty true
  check "a CR LF in the path is refused" (parsed "/repos/up/proj/x%0d%0aHost:%20y").toOption.isNone
  check "so is an encoded slash" (parsed "/repos/a%2Fb/proj").toOption.isNone
  check "and a dot segment" (parsed "/repos/bot/proj/../../up/secret").toOption.isNone
  let sentAs (t : String) := (parsed t).toOption.map (·.originTarget)
  checkEq "the target sent upstream is the segments, re-encoded"
    (sentAs "/repos/up/proj/issues/1/labels/p%20high") (some "/repos/up/proj/issues/1/labels/p%20high")
  checkEq "and UTF-8 survives the round trip"
    (sentAs "/repos/up/proj/contents/caf%C3%A9.md") (some "/repos/up/proj/contents/caf%C3%A9.md")
  checkEq "a comment ends at a carriage return"
    (ops "query A { a } #\rmutation B { b }") (some [("query", "A"), ("mutation", "B")])
  let mutation := "{\"query\":\"mutation { addStar(input: {}) { clientMutationId } }\"}"
  for ct in ["text/plain", "application/x-www-form-urlencoded", "application/graphql+json"] do
    checkEq s!"a mutation labelled {ct} is still read, and refused"
      (spentOn (choose registry token "POST" "api.github.com" "/graphql" mutation (some ct))) none
  checkEq "a duplicated query key is refused"
    (api "POST" "/graphql" "{\"query\":\"query { a }\",\"query\":\"mutation { b }\"}") none
  checkEq "a duplicated head is refused"
    (api "POST" "/repos/up/proj/pulls" "{\"head\":\"bot:x\",\"head\":\"evil:x\",\"base\":\"main\"}") none
  checkEq "a duplicated review event is refused"
    (api "POST" "/repos/up/proj/pulls/7/reviews" "{\"event\":\"COMMENT\",\"event\":\"APPROVE\"}") none
  checkEq "labels as objects are labels"
    (api "POST" "/repos/up/proj/issues/12/labels" "{\"labels\":[{\"name\":\"p-high\"}]}") none
  checkEq "a label as a bare string is a label"
    (api "POST" "/repos/up/proj/issues/12/labels" "\"p-high\"") none
  checkEq "labels sent as text are still read"
    (spentOn (choose registry token "POST" "api.github.com" "/repos/up/proj/issues/12/labels"
      "{\"labels\":[\"p-high\"]}" (some "text/plain"))) none
  checkEq "a pull request naming a head_repo is refused"
    (api "POST" "/repos/up/proj/pulls" "{\"head\":\"bot:x\",\"head_repo\":\"other\",\"base\":\"main\"}") none
  checkEq "a push sent without its content type is still read"
    (spentOn (choose registry token "POST" "github.com" "/bot/proj.git/git-receive-pack"
      (Bytes.toStringLossy (deleteBody ["refs/heads/main"])) none)) none
  let plainBody : Bytes := Bytes.ofString "x"
  checkEq "nothing past a body\x27s length is part of it"
    ((Proxy.splitAtFraming (.length 1) (plainBody ++ Bytes.ofString "GET / HTTP/1.1\r\n\r\n")).2.size) 18
  group "creating a repository"
  let creator ← match orchestraToken ["orchestra-github"]
      (base ++ ["task_tool(\"create_repository\")", "task_org(\"bot\")"]) with
    | .ok t => pure t
    | .error e => do check "a creating token can be issued" false e; return ()
  checkEq "creating one in the job's organisation, on the App's token"
    (api "POST" "/orgs/bot/repos" "{\"name\":\"new-thing\",\"private\":true}" (t := creator)) app
  checkEq "not elsewhere"
    (api "POST" "/orgs/up/repos" "{\"name\":\"new-thing\"}" (t := creator)) none
  checkEq "not with a name GitHub would change"
    (api "POST" "/orgs/bot/repos" "{\"name\":\"new thing\"}" (t := creator)) none
  checkEq "not without the tool" (api "POST" "/orgs/bot/repos" "{\"name\":\"new-thing\"}") none
  checkEq "and before it exists, it cannot be pushed to"
    (push "bot/new-thing" "refs/heads/main" (t := creator)) none
  let created := [Facts.fact "created_repository" [.str "bot", .str "new-thing"]]
  checkEq "once created, the token that made it may push to it"
    (push "bot/new-thing" "refs/heads/main" (t := creator) (remembered := created)) app
  let rememberedFacts := manifest.remember
    { method := "POST", scheme := "https", host := "api.github.com", port := 443
      path := "/orgs/bot/repos", segments := #["orgs", "bot", "repos"], query := #[]
      headers := #[], bodyPrefix := ByteArray.empty, bodyComplete := true, bodySize := none }
    (some (Json.obj [("name", .str "new-thing")]).toValue)
  checkEq "and what a creation is remembered as"
    (rememberedFacts.map (·.predicate.name)) ["created_repository"]
  check "a token cannot claim to have created one"
    (orchestraToken ["orchestra-github"] ["created_repository(\"bot\", \"x\")"]).toOption.isNone

  group "credential routes"
  let routed ← match Policy.Grant.ofToml ((← example? "examples/orchestra/grants/orchestra-github.toml")
      ++ "\n[[credential_route]]\nresources = [\"up/*\"]\ncredential = \"github/pat-up\"\n\n\
          [[credential_route]]\nresources = [\"up/special\"]\nanonymous = true\n") with
    | .ok g => pure g
    | .error e => do check "a grant with routes loads" false e; return ()
  checkEq "a route's credential is spendable" (routed.spendable.contains "github/pat-up") true
  checkEq "an owner route beats the rules"
    (routed.chooseCredential ["up/proj"] ["github/orchestra-pat"]) (some "github/pat-up")
  checkEq "an exact route beats an owner route" (routed.chooseCredential ["up/special"] []) none
  checkEq "the rules choose where no route matches"
    (routed.chooseCredential ["bot/proj"] ["github/orchestra-app"]) (some "github/orchestra-app")
  checkEq "a derived credential the grant may not spend is ignored"
    (routed.chooseCredential ["x/y"] ["github/root"]) none
  checkEq "and the fallback is the grant's own" (routed.chooseCredential [] []) none
  check "an organisation is matched by its owner pattern"
    (Policy.resourceMatch "acme/*" "acme" == some 2)

  group "a credential cannot be chosen from an appended block"
  -- A bearer can append a block of their own by hand, with facts in it.  Biscuit
  -- keeps those from satisfying the grant, but they reach the evaluated world, and
  -- a `use_credential` among them must not pick the credential.
  let forged ← match orchestraToken ["orchestra-github"] base with
    | .error e => do check "a token to forge on can be issued" false e; return ()
    | .ok t =>
      match BlockBuilder.code {} "use_credential(\"github/orchestra-pat\");" with
      | .error e => do check "a forged block can be built" false e.toString; return ()
      | .ok b =>
        match Biscuit.append t (fixedKey 13) b with
        | .ok f => pure f
        | .error e => do check "a forged block can be appended" false e.toString; return ()
  checkEq "an anonymous read stays anonymous"
    (api "GET" "/repos/torvalds/linux" (t := forged)) anonymous

  group "attenuation narrows the token"
  let attenuation := "check if operation(\"fetch\") or operation(\"discover\");"
  let narrowed ← match orchestraToken ["orchestra-github"] (base ++ ["task_tool(\"comment\")"]) |>.bind
      (Token.attenuate · attenuation (fixedKey 11)) with
    | .ok n => pure n
    | .error e => do check "a job's token can be attenuated" false e; return ()
  checkEq "a narrowed token may still fetch"
    (git "/up/proj.git/info/refs?service=git-upload-pack" (t := narrowed)) pat
  checkEq "and may not comment"
    (api "POST" "/repos/up/proj/issues/7/comments" "{\"body\":\"hi\"}" (t := narrowed)) none

end KleisTests
