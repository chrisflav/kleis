import KleisTests.Orchestra

/-! # Specs, narrowings, cards and setup

The shipped extensions under `extensions/`, with accounts made up for the test, and specs
compiled against them — decided through the same selection and authorizer the proxy uses. -/

namespace KleisTests

open Kleis LeanBiscuit
open LeanBiscuit.Token (Biscuit AuthorizerBuilder Authorizer)

/-- An extension from the repository, its manifest claiming these hosts if they are dynamic. -/
private def shipped (name : String) (hosts : List String) :
    IO (Service.Extension × Service.Manifest) := do
  let dir := System.FilePath.mk "extensions" / name
  let e ← match Service.Extension.ofToml (← IO.FS.readFile (dir / "extension.toml"))
      (← IO.FS.readFile (dir / "manifest.toml")) dir with
    | .ok e => pure e
    | .error err => throw (IO.userError s!"{name}: {err}")
  let m ← match e.manifest hosts with
    | .ok m => pure m
    | .error err => throw (IO.userError s!"{name}: {err}")
  match e.check m with
  | .ok () => pure (e, m)
  | .error err => throw (IO.userError s!"{name}: {err}")

private def account (name service : String) (hosts : List String := []) : Credential.Record :=
  { name, service, provider := "static", config := .obj [], created := 0, nonce := ""
    ciphertext := "", secretFile := some "/dev/null", hosts }

private def secretary : String := "
spec secretary
  description \"Reads and files Christian's mail and keeps his calendar.\"
  max_ttl 24h

  account mail/christian
    allow read, flag, move
    allow send where recipient all ends_with \"@merten.dev\"

  account caldav/christian
    allow read
    allow write, delete where path starts_with \"calendars/christian/personal/\"
"

private def alice : String := "
spec alice
  max_ttl 8h
  # Two Zulip accounts, on two servers.
  account zulip/alice-home
    allow read, send_message
  account zulip/alice-work
    allow read
"

/-- A registry of the shipped extensions, these accounts, and these specs. -/
private def registryWith (specs : List String) (grants : List String := []) :
    IO Service.Registry := do
  let credentials : Array Credential.Record := #[
    account "mail/christian" "mail",
    account "caldav/christian" "caldav" ["dav.example.org"],
    account "zulip/alice-home" "zulip" ["zulip.home.example"],
    account "zulip/alice-work" "zulip" ["chat.work.example"]]
  let exts ← [("mail", []), ("caldav", ["dav.example.org"]),
              ("zulip", ["zulip.home.example", "chat.work.example"])].mapM fun (n, h) => shipped n h
  let grantFiles ← grants.mapM fun src => match Policy.Grant.ofToml src with
    | .ok g => pure g
    | .error e => throw (IO.userError e)
  let env : Spec.Env := { extensions := exts, credentials, grants := grantFiles.toArray }
  let compiled ← specs.mapM fun src => match Spec.load src env with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  pure { manifests := (exts.map (·.2)).toArray
         grants := grantFiles.toArray ++ (compiled.flatMap fun s => s.accounts.map (·.grant)).toArray
         extensions := (exts.map (·.1)).toArray
         specs := compiled.toArray }

private def specToken (specs : List String) (grants : List String := [])
    (checks : List Builder.Check := []) : Except String Biscuit := do
  let (t, _) ← Token.issue (fixedKey 7)
    { grants, specs, bearer := "test", lifetime := 3600, extraChecks := checks }
    1700000000 (fixedKey 9)
  pure t

/-- Does a token still hold where there is no request at all — the daemon's own endpoints,
a passthrough tunnel? The same evaluation as `Proxy.tokenHolds`. -/
private def holdsWithoutRequest (token : Biscuit) : Bool :=
  let builder : AuthorizerBuilder := {
    facts := [⟨⟨"time", [.date 1700000100]⟩⟩]
    rules := [], checks := [], scopes := []
    policies := [{ queries := [{ head := ⟨"query", []⟩, body := [], expressions := [], scopes := [] }],
                   kind := .allow }]
    externs := Policy.standard, limits := {} }
  match Authorizer.build builder token with
  | .error _ => false
  | .ok a => (Authorizer.authorizeWithState a).1 |>.isOk

private def compileErr (src : String) : IO (Option String) := do
  let credentials : Array Credential.Record := #[
    account "mail/christian" "mail", account "zulip/nohosts" "zulip"]
  let exts ← [("mail", []), ("zulip", [])].mapM fun (n, h) => shipped n h
  pure <| match Spec.load src { extensions := exts, credentials, grants := #[] } with
    | .ok _ => none
    | .error e => some e

/-- The facts a manifest's routes emit for a request, printed. -/
private def routeFacts (m : Service.Manifest) (method host path : String) : List String :=
  let request : Model.Request := {
    method, scheme := "https", host, port := 443
    path := Str.pathOnly path, segments := Str.pathSegments path, query := Str.parseQuery path
    headers := #[("host", host)], bodyPrefix := ByteArray.empty, bodyComplete := true
    bodySize := some 0 }
  (m.routes.flatMap fun rt => (rt.apply request none).getD []).map (Builder.Predicate.print ·.predicate)

/-- The orchestra example's review specs, against the shipped GitHub and diff-reviewer
extensions, with the accounts they name made up. -/
private def reviewRegistry : IO Service.Registry := do
  let credentials : Array Credential.Record := #[
    account "diff-reviewer/agent" "diff-reviewer" ["reviews.example"],
    account "github/orchestra-app" "github", account "github/orchestra-pat" "github",
    account "github/chrisflav" "github"]
  let exts ← [("github", []), ("diff-reviewer", ["reviews.example"])].mapM fun (n, h) => shipped n h
  let grant ← match Policy.Grant.ofToml
      (← IO.FS.readFile "examples/orchestra/grants/orchestra-reviewer-github.toml") with
    | .ok g => pure g
    | .error e => throw (IO.userError e)
  let env : Spec.Env := { extensions := exts, credentials, grants := #[grant] }
  let compiled ← ["reviewer", "diff-reviewer-poster"].mapM fun n => do
    match Spec.load (← IO.FS.readFile s!"examples/orchestra/specs/{n}.kleis") env with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{n}: {e}")
  pure { manifests := (exts.map (·.2)).toArray
         grants := #[grant] ++ (compiled.flatMap fun s => s.accounts.map (·.grant)).toArray
         extensions := (exts.map (·.1)).toArray
         specs := compiled.toArray }

/-- A task token from a spec, as `/.kleis/v1/derive` writes it: the task's facts in the
authority block. -/
private def taskToken (spec : String) (facts : List String)
    (issuedBy : Option String := some "orchestra") : Except String Biscuit := do
  let facts ← facts.mapM Token.factOfSource
  let (t, _) ← Token.issue (fixedKey 7)
    { grants := [], specs := [spec], bearer := "orchestra:t-1", lifetime := 3600, issuedBy, extraFacts := facts }
    1700000000 (fixedKey 9)
  pure t

/-- A review with `n` inline comments, in the shape the platform posts to GitHub: six fields
each, and a body of `size` bytes with a suggestion in it. -/
private def bigReview (n : Nat) (size : Nat := 8000) : String :=
  let comment (i : Nat) := "{\"path\":\"Mathlib/Foo/Bar" ++ toString i ++ ".lean\",\"start_line\":" ++
    toString i ++ ",\"line\":" ++ toString (i + 1) ++ ",\"side\":\"RIGHT\"," ++
    "\"start_side\":\"RIGHT\",\"body\":\"" ++ String.ofList (List.replicate size 'x') ++
    "\\n```suggestion\\nexact h\\n```\"}"
  "{\"commit_id\":\"abc\",\"event\":\"COMMENT\",\"body\":\"b\",\"comments\":[" ++
    ",".intercalate ((List.range n).map comment) ++ "]}"

/-- A submission to the platform with `n` inline comments, in the agent API's shape: seven
fields each, a body and a suggestion of `size` bytes between them. -/
private def agentReview (n : Nat) (size : Nat := 8000) : String :=
  let text (k : Nat) := String.ofList (List.replicate k 'x')
  let comment (i : Nat) := "{\"file\":\"Mathlib/Foo/Bar" ++ toString i ++ ".lean\",\"start_line\":" ++
    toString i ++ ",\"end_line\":" ++ toString (i + 1) ++ ",\"category\":\"style\"," ++
    "\"severity\":\"minor\",\"body\":\"" ++ text (size - size / 3) ++ "\",\"suggestion\":\"" ++
    text (size / 3) ++ "\"}"
  "{\"headSha\":\"abc\",\"prType\":null,\"review\":{\"decision\":\"comment\",\"body\":\"b\"," ++
    "\"comments\":[" ++ ",".intercalate ((List.range n).map comment) ++ "]}}"

/-- Whether a request was refused, and the reason says `needle`. -/
private def refusedFor (c : Except String Policy.Choice) (needle : String) : Bool :=
  match c with
  | .ok c => !c.outcome.allowed && (c.reason.splitOn needle).length > 1
  | .error _ => false

/-- Bodies built to be expensive to decide, each about `bytes` long: its name, and the body. -/
private def costlyBodies (bytes : Nat) : List (String × String) :=
  let rep (k : Nat) (t : String) : String := String.join (List.replicate k t)
  let list (unit : String) : String :=
    let k := bytes / (unit.length + 1)
    "[" ++ ",".intercalate (List.replicate k unit) ++ "]"
  [("deep arrays", rep (bytes / 2) "[" ++ rep (bytes / 2) "]"),
   ("deep objects", rep (bytes / 6) "{\"a\":" ++ "1" ++ rep (bytes / 6) "}"),
   ("empty arrays", list "[]"),
   ("empty objects", list "{}"),
   ("mixed containers", list "[{\"a\":[[]]},{}]"),
   ("scalars", list "1"),
   ("keys", "{" ++ ",".intercalate ((List.range (bytes / 10)).map fun i =>
      "\"k" ++ toString i ++ "\":1") ++ "}"),
   ("ref updates", "{\"updates\":" ++ list "{\"ref\":\"refs/heads/x\",\"create\":true,\"delete\":true}" ++ "}"),
   ("labels", "{\"labels\":" ++ list "\"x\"" ++ "}")]

/-- Bodies built to be expensive to decide that stay just within `facts` facts, so they are
read and evaluated rather than refused as truncated. -/
private def costlyWithin (facts : Nat) : List (String × String) :=
  let list (k : Nat) (unit : String) : String := "[" ++ ",".intercalate (List.replicate k unit) ++ "]"
  let n := facts - 3
  [("scalars", list n "1"),
   ("strings", list n "\"x\""),
   ("trues", list n "true"),
   ("empty arrays", list (n / 2 - 1) "[]"),
   ("keys", "{" ++ ",".intercalate ((List.range n).map fun i => "\"k" ++ toString i ++ "\":1") ++ "}"),
   ("ref updates", "{\"updates\":" ++
      list (n / 6) "{\"ref\":\"refs/heads/x\",\"create\":true,\"delete\":true}" ++ "}"),
   ("nesting 63 deep", String.join (List.replicate 63 "[") ++ "1" ++ String.join (List.replicate 63 "]"))]

def specTests : IO Unit := do
  group "the shipped extensions load and agree with their manifests"
  for (n, h) in [("github", []), ("zulip", ["z.example"]), ("caldav", ["d.example"]), ("mail", []),
                 ("taxis", ["t.example"]), ("diff-reviewer", ["r.example"])] do
    let ok ← try let _ ← shipped n h; pure true catch _ => pure false
    check s!"{n}" ok

  group "a spec that does not say what it means is refused at load"
  let refused (name src : String) (needle : String) : IO Unit := do
    match ← compileErr src with
    | some e => check name ((e.splitOn needle).length > 1) e
    | none => check name false "it loaded"
  refused "no max_ttl" "spec s\n  account mail/christian\n    allow read\n" "max_ttl"
  refused "an operation the extension does not know"
    "spec s\n  max_ttl 1h\n  account mail/christian\n    allow delete_everything\n" "neither an operation"
  refused "a field the extension does not know"
    "spec s\n  max_ttl 1h\n  account mail/christian\n    allow send where colour is \"red\"\n" "not a field"
  refused "a multi-valued field without all or any"
    "spec s\n  max_ttl 1h\n  account mail/christian\n    allow send where recipient ends_with \"@x\"\n" "several values"
  refused "an `all` whose operations another line also allows"
    "spec s\n  max_ttl 1h\n  account mail/christian\n    allow send where recipient all ends_with \"@x\"\n    allow send\n" "another line"
  refused "an account of a dynamic-host service without hosts"
    "spec s\n  max_ttl 1h\n  account zulip/nohosts\n    allow read\n" "must name its `hosts`"
  refused "an account nobody installed"
    "spec s\n  max_ttl 1h\n  account mail/nobody\n    allow read\n" "no credential"
  refused "a type mismatch" "spec s\n  max_ttl 1h\n  account mail/christian\n    allow read where mailbox is 3\n" "compares with a int"

  group "the secretary"
  let reg ← registryWith [secretary]
  let tok ← match specToken ["secretary"] with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  let send (body : String) := choose reg tok "POST" "kleis-mail" "/send" body (some "application/json")
  checkEq "reads its mail, on its account"
    (spentOn (choose reg tok "GET" "kleis-mail" "/mailboxes/INBOX/messages")) (some "mail/christian")
  checkEq "flags a message"
    (spentOn (choose reg tok "POST" "kleis-mail" "/mailboxes/INBOX/messages/4/flags"
      "{\"add\": [\"\\\\Seen\"]}" (some "application/json"))) (some "mail/christian")
  checkEq "sends within merten.dev"
    (spentOn (send "{\"to\": [\"a@merten.dev\"], \"cc\": [\"b@merten.dev\"], \"subject\": \"s\", \"text\": \"t\"}"))
    (some "mail/christian")
  checkEq "does not send outside it" (spentOn (send "{\"to\": [\"a@example.org\"], \"text\": \"t\"}")) none
  checkEq "not even by bcc"
    (spentOn (send "{\"to\": [\"a@merten.dev\"], \"bcc\": [\"spy@example.org\"], \"text\": \"t\"}")) none
  checkEq "nor as a bare string" (spentOn (send "{\"to\": \"spy@example.org\", \"text\": \"t\"}")) none
  checkEq "and sends nothing with no recipient" (spentOn (send "{\"subject\": \"s\", \"text\": \"t\"}")) none
  checkEq "reads the calendar"
    (spentOn (choose reg tok "PROPFIND" "dav.example.org" "/")) (some "caldav/christian")
  checkEq "writes an event in its calendar"
    (spentOn (choose reg tok "PUT" "dav.example.org" "/calendars/christian/personal/e.ics")) (some "caldav/christian")
  checkEq "but not in another"
    (spentOn (choose reg tok "PUT" "dav.example.org" "/calendars/christian/work/e.ics")) none
  checkEq "and creates no calendars"
    (spentOn (choose reg tok "MKCALENDAR" "dav.example.org" "/calendars/christian/new/")) none
  check "a service the spec has no account for is refused, and says so"
    (match choose reg tok "GET" "zulip.home.example" "/api/v1/users/me" with
     | .error e => (e.splitOn "no account for `zulip`").length > 1
     | .ok _ => false)

  group "a compiled grant cannot be reached without its spec"
  let byName ← match specToken [] ["secretary/mail/christian"] with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "naming it as a grant gets nothing"
    (spentOn (choose reg byName "GET" "kleis-mail" "/mailboxes")) none

  group "several accounts of one service, on several servers"
  let reg2 ← registryWith [alice]
  let tokA ← match specToken ["alice"] with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "home server, home account"
    (spentOn (choose reg2 tokA "GET" "zulip.home.example" "/api/v1/users/me")) (some "zulip/alice-home")
  checkEq "work server, work account"
    (spentOn (choose reg2 tokA "GET" "chat.work.example" "/api/v1/users/me")) (some "zulip/alice-work")
  checkEq "sends at home"
    (spentOn (choose reg2 tokA "POST" "zulip.home.example" "/api/v1/messages"
      "type=stream&to=general&topic=t&content=hi" (some "application/x-www-form-urlencoded")))
    (some "zulip/alice-home")
  checkEq "but only reads at work"
    (spentOn (choose reg2 tokA "POST" "chat.work.example" "/api/v1/messages"
      "type=stream&to=general&topic=t&content=hi" (some "application/x-www-form-urlencoded"))) none
  checkEq "deletes nothing anywhere"
    (spentOn (choose reg2 tokA "DELETE" "zulip.home.example" "/api/v1/messages/5")) none

  group "a spec including a grant file"
  let includer := "spec worker\n  max_ttl 2h\n  grant plain-mail\n"
  let plain := "name = \"plain-mail\"\nservice = \"mail\"\ncredential = \"mail/christian\"\nmax_lifetime = \"1h\"\ndatalog = '''\ncheck if operation(\"list_mailboxes\");\nallow if grant(\"plain-mail\");\n'''\n"
  let reg3 ← registryWith [includer] [plain]
  let tokW ← match specToken ["worker"] with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "decides as if the token named it"
    (spentOn (choose reg3 tokW "GET" "kleis-mail" "/mailboxes")) (some "mail/christian")
  checkEq "and as narrowly" (spentOn (choose reg3 tokW "GET" "kleis-mail" "/mailboxes/INBOX/messages")) none
  match reg3.spec? "worker" with
  | some s => checkEq "a token of it lives no longer than the grant allows" (reg3.specLifetime s) 3600
  | none => check "the spec loaded" false

  group "narrowing"
  let narrowed ← match Narrow.compile reg ["mail: only read"] with
    | .ok cs => pure cs
    | .error e => throw (IO.userError e)
  let tokN ← match specToken ["secretary"] [] narrowed with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "still reads" (spentOn (choose reg tokN "GET" "kleis-mail" "/mailboxes")) (some "mail/christian")
  checkEq "no longer sends"
    (spentOn (choose reg tokN "POST" "kleis-mail" "/send" "{\"to\": [\"a@merten.dev\"], \"text\": \"t\"}"
      (some "application/json"))) none
  checkEq "leaves the calendar alone"
    (spentOn (choose reg tokN "PUT" "dav.example.org" "/calendars/christian/personal/e.ics")) (some "caldav/christian")
  check "and still holds where there is no request" (holdsWithoutRequest tokN)
  check "a narrowing naming an unknown operation is refused"
    (match Narrow.compile reg ["mail: only teleport"] with | .error _ => true | .ok _ => false)
  check "as is one for a service nobody has"
    (match Narrow.compile reg ["fax: only read"] with | .error _ => true | .ok _ => false)
  let confined ← match Narrow.compile reg ["services: mail"] with
    | .ok cs => pure cs
    | .error e => throw (IO.userError e)
  let tokS ← match specToken ["secretary"] [] confined with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "confined to mail, it still reads mail"
    (spentOn (choose reg tokS "GET" "kleis-mail" "/mailboxes")) (some "mail/christian")
  checkEq "but no longer reaches the calendar its spec has"
    (spentOn (choose reg tokS "PROPFIND" "dav.example.org" "/")) none
  check "and still holds where there is no request" (holdsWithoutRequest tokS)
  check "confining to a service nobody has is refused"
    (match Narrow.compile reg ["services: mail, fax"] with | .error _ => true | .ok _ => false)

  group "cards"
  let card := Card.render reg tok [{ revocationIds := [], grants := [], bearer := "test"
                                     issued := 1700000000, expires := 1700003600
                                     narrowings := ["mail: only read"] }]
  for needle in ["acts as \"secretary\"", "Reads and files", "2023-11-14 23:13 UTC",
                 "send mail, only if every recipient's address ends with \"@merten.dev\"",
                 "Calendar — caldav/christian on dav.example.org",
                 "narrowed further: mail: only read"] do
    check s!"says {needle}" ((card.splitOn needle).length > 1) card

  group "setup"
  match Card.setup reg2 tokA with
  | .error e => check "setup" false e
  | .ok (_, files) =>
    let paths := files.map (·.path)
    check "a zuliprc per server" (paths.contains ".config/zulip/zulip.home.example.zuliprc"
      && paths.contains ".config/zulip/chat.work.example.zuliprc") (toString paths)
    check "and a default one" (paths.contains ".zuliprc")
    check "with placeholders, never a key"
      (files.all fun f => (f.content.splitOn "key=kleis").length > 1)
  check "a setup path may not climb out of home"
    (!Service.safeRelativePath "../.ssh/authorized_keys" && !Service.safeRelativePath "/etc/passwd"
      && !Service.safeRelativePath "a/../../b" && Service.safeRelativePath ".config/zulip/x.zuliprc")

  group "the diff-reviewer extension"
  let (_, drm) ← shipped "diff-reviewer" ["reviews.example"]
  let agent := "/api/agent/v1/repos/acme/widgets/pulls/7"
  let about := ["repository(\"acme\", \"widgets\")", "pull(7)"]
  checkEq "the job is a read of that pull request"
    (routeFacts drm "GET" "reviews.example" agent) (["operation(\"read\")"] ++ about)
  checkEq "so is its diff"
    (routeFacts drm "GET" "reviews.example" s!"{agent}/diff") (["operation(\"read\")"] ++ about)
  checkEq "a review is submit_review"
    (routeFacts drm "POST" "reviews.example" s!"{agent}/review") (["operation(\"submit_review\")"] ++ about)
  for (m, path) in [("GET", "/api/v1/jobs"), ("POST", "/api/v1/jobs/3/post"), ("POST", "/api/login"),
                    ("GET", "/"), ("GET", "/api/agent/v1/repos/acme/widgets/pulls"),
                    ("GET", "/api/agent/v1/repos/acme/widgets/pulls/seven"),
                    ("GET", s!"{agent}/review"), ("POST", agent), ("POST", s!"{agent}/diff"),
                    ("PUT", s!"{agent}/review"), ("DELETE", s!"{agent}/review"),
                    ("GET", s!"{agent}/diff/more")] do
    checkEq s!"{m} {path} is matched by nothing" (routeFacts drm m "reviews.example" path) []

  group "the reviewer"
  let rr ← reviewRegistry
  -- Read-only, and given tools anyway: none of them reaches GitHub through this spec.
  let task := ["task_fork(\"bot\", \"proj\")", "task_upstream(\"up\", \"proj\")", "task_issue(7)",
    "task_tool(\"create_pr\")", "task_tool(\"comment\")", "task_tool(\"label_issue\")",
    "task_tool(\"merge_pr\")", "task_pr_labels([\"orchestra\"])", "task_label_any(true)"]
  let rt ← match taskToken "reviewer" task with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  let dr (method path : String) (body : String := "") (t := rt) :=
    spentOn (choose rr t method "reviews.example" path body
      (if body.isEmpty then none else some "application/json"))
  let review := "{\"headSha\": \"abc\", \"prType\": null, \"review\": " ++
    "{\"decision\": \"comment\", \"body\": \"b\", \"comments\": []}}"
  let own := "/api/agent/v1/repos/up/proj/pulls/7"
  let agentToken := some "diff-reviewer/agent"
  checkEq "reads its own pull request's job, on the agent token" (dr "GET" own) agentToken
  checkEq "and its diff" (dr "GET" s!"{own}/diff") agentToken
  checkEq "submits its review" (dr "POST" s!"{own}/review" review) agentToken
  checkEq "not a review nobody can read" (dr "POST" s!"{own}/review" "{\"headSha\":") none
  checkEq "not another pull request's job" (dr "GET" "/api/agent/v1/repos/up/proj/pulls/8") none
  checkEq "nor a review of it" (dr "POST" "/api/agent/v1/repos/up/proj/pulls/8/review" review) none
  checkEq "nor another repository's pull request of that number"
    (dr "GET" "/api/agent/v1/repos/other/proj/pulls/7") none
  checkEq "nor its fork's" (dr "POST" "/api/agent/v1/repos/bot/proj/pulls/7/review" review) none
  checkEq "nor another repository of its upstream's owner"
    (dr "POST" "/api/agent/v1/repos/up/other/pulls/7/review" review) none
  checkEq "a review of 200 comments is submitted"
    (dr "POST" s!"{own}/review" (agentReview 200)) agentToken
  -- 1856 facts: four scalars and three containers for the submission, nine a comment.
  check "one of 206 is too many facts, and refused as unread"
    (refusedFor (choose rr rt "POST" "reviews.example" s!"{own}/review" (agentReview 206)
      (some "application/json")) "body_truncated")
  checkEq "nor the scripts' API" (dr "GET" "/api/v1/jobs") none
  checkEq "nor the login" (dr "POST" "/api/login" "{\"password\": \"x\"}") none
  check "the agent token goes to no other server"
    (spentOn (choose rr rt "GET" "other.example" own)).isNone
  let factless ← match taskToken "reviewer" [] with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "a token without the task's pull request reaches no job" (dr "GET" own (t := factless)) none
  let wrongIssuer ← match taskToken "reviewer" task (issuedBy := some "somebody") with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  let oid := String.ofList (List.replicate 40 'a')
  let gh (method host path : String) (body : String := "") (t := rt) :=
    spentOn (choose rr t method host path body (if body.isEmpty then none else some "application/json"))
  let push (repo : String) (t := rt) :=
    spentOn (choose rr t "POST" "github.com" s!"/{repo}.git/git-receive-pack"
      (Bytes.toStringLossy (pushBody [(oid, "refs/heads/x")]))
      (some "application/x-git-receive-pack-request"))
  let pat := some "github/orchestra-pat"
  checkEq "fetches the upstream on the operator's token"
    (gh "GET" "github.com" "/up/proj.git/info/refs?service=git-upload-pack") pat
  checkEq "reads its pull request through the API" (gh "GET" "api.github.com" "/repos/up/proj/pulls/7") pat
  checkEq "reads a public repository anonymously"
    (gh "GET" "api.github.com" "/repos/torvalds/linux") (some "-")
  checkEq "runs a GraphQL query"
    (gh "POST" "api.github.com" "/graphql" "{\"query\":\"query { viewer { login } }\"}")
    (some "github/orchestra-app")
  checkEq "but not under another issuer's name"
    (gh "GET" "api.github.com" "/repos/up/proj/pulls/7" (t := wrongIssuer)) none
  checkEq "pushes nowhere: not to its fork" (push "bot/proj") none
  checkEq "nor to the upstream" (push "up/proj") none
  checkEq "nor starts a push"
    (gh "GET" "github.com" "/bot/proj.git/info/refs?service=git-receive-pack") none
  let writes : List (String × String × String) := [
    ("POST", "/repos/up/proj/pulls/7/reviews", "{\"event\":\"COMMENT\",\"body\":\"x\"}"),
    ("POST", "/repos/up/proj/pulls/7/reviews", "{\"event\":\"APPROVE\"}"),
    ("POST", "/repos/up/proj/pulls/7/comments", "{\"body\":\"x\"}"),
    ("POST", "/repos/up/proj/pulls/7/comments/9/replies", "{\"body\":\"x\"}"),
    ("POST", "/repos/up/proj/issues/7/comments", "{\"body\":\"x\"}"),
    ("POST", "/repos/up/proj/issues/7/labels", "{\"labels\":[\"orchestra\"]}"),
    ("PUT", "/repos/up/proj/issues/7/labels", "{\"labels\":[\"orchestra\"]}"),
    ("DELETE", "/repos/up/proj/issues/7/labels/orchestra", ""),
    ("POST", "/repos/up/proj/labels", "{\"name\":\"orchestra\"}"),
    ("POST", "/repos/up/proj/pulls", "{\"head\":\"bot:x\",\"base\":\"main\"}"),
    ("POST", "/repos/bot/proj/pulls", "{\"head\":\"x\",\"base\":\"main\"}"),
    ("PATCH", "/repos/up/proj/pulls/7", "{\"title\":\"t\"}"),
    ("PUT", "/repos/up/proj/pulls/7/merge", "{}"),
    ("POST", "/orgs/bot/repos", "{\"name\":\"new\"}"),
    ("POST", "/graphql", "{\"query\":\"mutation { addComment(input: {}) { clientMutationId } }\"}")]
  for (m, path, body) in writes do
    checkEq s!"refuses {m} {path}" (gh m "api.github.com" path body) none
  -- A repository the App is installed on is worked on directly: fork and upstream are one.
  let direct ← match taskToken "reviewer"
      ["task_fork(\"up\", \"proj\")", "task_upstream(\"up\", \"proj\")", "task_issue(7)",
       "task_tool(\"create_pr\")", "task_tool(\"comment\")"] with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  checkEq "with its fork its upstream, it still cannot push there" (push "up/proj" (t := direct)) none
  checkEq "nor open a pull request there"
    (gh "POST" "api.github.com" "/repos/up/proj/pulls" "{\"head\":\"x\",\"base\":\"main\"}"
      (t := direct)) none
  checkEq "nor review" (gh "POST" "api.github.com" "/repos/up/proj/pulls/7/reviews"
    "{\"event\":\"COMMENT\",\"body\":\"x\"}" (t := direct)) none
  checkEq "but reads it" (gh "GET" "api.github.com" "/repos/up/proj/pulls/7" (t := direct))
    (some "github/orchestra-app")
  match Card.setup rr rt with
  | .error e => check "setup" false e
  | .ok (_, files) =>
    match files.find? (·.path == ".config/diff-reviewer/agent.json") with
    | none => check "setup writes the agent's config" false (toString (files.map (·.path)))
    | some f =>
      checkEq "setup writes the agent's config, with the placeholder token" f.content
        "{\"url\": \"https://reviews.example\", \"token\": \"kleis\"}\n"

  group "the diff-reviewer platform, posting"
  let pt ← match taskToken "diff-reviewer-poster" [] (issuedBy := none) with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  let post (method path : String) (body : String := "") :=
    spentOn (choose rr pt method "api.github.com" path body
      (if body.isEmpty then none else some "application/json"))
  let chris := some "github/chrisflav"
  let posted := "{\"commit_id\":\"abc\",\"event\":\"COMMENT\",\"body\":\"b\",\"comments\":" ++
    "[{\"path\":\"a.lean\",\"line\":3,\"side\":\"RIGHT\",\"body\":\"c\"}]}"
  checkEq "posts a review on a listed repository, on Christian's token"
    (post "POST" "/repos/chrisflav/kleis/pulls/7/reviews" posted) chris
  checkEq "and an inline comment"
    (post "POST" "/repos/chrisflav/kleis/pulls/7/comments" "{\"body\":\"c\"}") chris
  checkEq "lists its open pull requests" (post "GET" "/repos/chrisflav/kleis/pulls?state=open") chris
  checkEq "reads one" (post "GET" "/repos/chrisflav/kleis/pulls/7") chris
  for path in ["/user", "/user/repos", "/search/issues?q=x", "/rate_limit", "/users/someone"] do
    checkEq s!"reads nothing about no repository: {path}" (post "GET" path) none
  checkEq "clones nothing, not even a listed repository"
    (spentOn (choose rr pt "GET" "github.com" "/chrisflav/kleis.git/info/refs?service=git-upload-pack")) none
  checkEq "posts a review of 200 comments"
    (post "POST" "/repos/chrisflav/kleis/pulls/7/reviews" (bigReview 200)) chris
  -- 1664 facts: three scalars and two containers for the review, eight a comment.
  check "not one of 208, which is too many facts, and refused as unread"
    (refusedFor (choose rr pt "POST" "api.github.com" "/repos/chrisflav/kleis/pulls/7/reviews"
      (bigReview 208) (some "application/json")) "body_truncated")
  checkEq "but one of 207"
    (post "POST" "/repos/chrisflav/kleis/pulls/7/reviews" (bigReview 207)) chris
  checkEq "posts no review on a repository not listed"
    (post "POST" "/repos/acme/widgets/pulls/7/reviews" posted) none
  -- Each of these is a substring of the listed name or contains it, so a list written as a
  -- string rather than a set would let some through.
  for repo in ["chrisflav/kleis-fork", "chrisflav/klei", "hrisflav/kleis", "ChrisFlav/kleis",
               "chrisflav/kleis.git", "chrisflav/kleis/x"] do
    checkEq s!"nor on {repo}" (post "POST" s!"/repos/{repo}/pulls/7/reviews" posted) none
  -- No route emits two repositories for one request, so only a world given a second one
  -- reaches the `reject`: an allowed review, with an unlisted repository beside it.
  checkEq "a request about an unlisted repository beside a listed one is refused"
    (spentOn (choose rr pt "POST" "api.github.com" "/repos/chrisflav/kleis/pulls/7/reviews" posted
      (some "application/json") [Facts.fact "repository" [.str "acme", .str "widgets"]])) none
  checkEq "nor reads one" (post "GET" "/repos/acme/widgets/pulls") none
  checkEq "comments on no issue"
    (post "POST" "/repos/chrisflav/kleis/issues/7/comments" "{\"body\":\"x\"}") none
  checkEq "merges nothing" (post "PUT" "/repos/chrisflav/kleis/pulls/7/merge" "{}") none
  checkEq "and runs no GraphQL"
    (post "POST" "/graphql" "{\"query\":\"query { viewer { login } }\"}") none

  group "bodies built to be expensive are refused quickly"
  -- Each shape at the default prefix and at the example's 2 MiB, through the platform's review
  -- route on GitHub and a job's on the platform. `choose` decodes the whole body, as the
  -- proxy does up to its prefix.
  let mut slowest : Nat := 0
  for bytes in [65536, 2097152] do
    for (name, body) in costlyBodies bytes do
      for (label, t, host, path) in [
          ("GitHub", pt, "api.github.com", "/repos/chrisflav/kleis/pulls/7/reviews"),
          ("diff-reviewer", rt, "reviews.example", "/api/agent/v1/repos/up/proj/pulls/7/review")] do
        let t0 ← IO.monoMsNow
        let refused ← IO.lazyPure fun _ =>
          (spentOn (choose rr t "POST" host path body (some "application/json"))).isNone
        let ms := (← IO.monoMsNow) - t0
        slowest := max slowest ms
        check s!"{name}, {bytes} bytes, to {label}: refused in {ms} ms" (refused && ms < 2000)
  for (label, t, host, path, limit) in [
      ("GitHub", pt, "api.github.com", "/repos/chrisflav/kleis/pulls/7/reviews", 1664),
      ("diff-reviewer", rt, "reviews.example", "/api/agent/v1/repos/up/proj/pulls/7/review", 1856)] do
    for (name, body) in costlyWithin limit do
      let t0 ← IO.monoMsNow
      let decided ← IO.lazyPure fun _ =>
        match choose rr t "POST" host path body (some "application/json") with
        | .ok c => (c.reason.splitOn "body_truncated").length == 1
        | .error _ => false
      let ms := (← IO.monoMsNow) - t0
      slowest := max slowest ms
      check s!"{name} within the limit, to {label}: read and decided in {ms} ms" (decided && ms < 2000)
  for (label, t, host, path, body) in [
      ("GitHub", pt, "api.github.com", "/repos/chrisflav/kleis/pulls/7/reviews", bigReview 207),
      ("diff-reviewer", rt, "reviews.example", "/api/agent/v1/repos/up/proj/pulls/7/review",
        agentReview 205)] do
    let t0 ← IO.monoMsNow
    let allowed ← IO.lazyPure fun _ =>
      (spentOn (choose rr t "POST" host path body (some "application/json"))).isSome
    let ms := (← IO.monoMsNow) - t0
    slowest := max slowest ms
    check s!"a review at the limit, to {label}: allowed in {ms} ms" (allowed && ms < 2000)
  check s!"the slowest of them took {slowest} ms" (slowest < 2000)

  group "every shape, read, decoded and decided in time"
  -- What a bearer can make kleis do with one body, at the default prefix and at the
  -- example's 2 MiB: read it, a few bytes at a time, decode it, and decide on it.  The
  -- bounds are generous for CI; what was measured is in the manifests' comments.
  let rep (n : Nat) (t : String) : String := String.join (List.replicate n t)
  let oid := String.ofList (List.replicate 40 'a')
  let shapes (n : Nat) : List (String × String × String × String × Option String) :=
    let api := "api.github.com"
    let keys := (List.range (n / 9)).map fun i => "\"k" ++ toString i ++ "\":0"
    let width := n / 60 / 8
    let level := ",".intercalate ((List.range width).map fun i => "\"a" ++ toString i ++ "\":1")
    [("digits", api, "/repos/up/proj/forks", "[" ++ rep (n - 2) "7" ++ "]", some "application/json"),
     ("floats", api, "/repos/up/proj/forks", "[" ++ ",".intercalate (List.replicate (n / 9) "1.5e-300") ++ "]",
       some "application/json"),
     ("\\u escapes", api, "/repos/up/proj/forks", "[\"" ++ rep ((n - 4) / 6) "\\u00e9" ++ "\"]",
       some "application/json"),
     ("surrogate pairs", api, "/repos/up/proj/forks", "[\"" ++ rep ((n - 4) / 12) "\\ud83d\\ude00" ++ "\"]",
       some "application/json"),
     ("a long string", api, "/repos/up/proj/forks", "[\"" ++ rep (n - 4) "x" ++ "\"]", some "application/json"),
     ("non-ASCII", api, "/repos/up/proj/forks", "[\"" ++ rep ((n - 4) / 4) "😀" ++ "\"]", some "application/json"),
     ("many keys", api, "/repos/up/proj/forks", "{" ++ ",".intercalate keys ++ "}", some "application/json"),
     ("one key repeated", api, "/repos/up/proj/forks", "{" ++ ",".intercalate (List.replicate (n / 6) "\"k\":0") ++ "}",
       some "application/json"),
     ("wide and 60 deep", api, "/repos/up/proj/forks", rep 60 ("{" ++ level ++ ",\"z\":") ++ "1" ++ rep 60 "}",
       some "application/json"),
     ("form, distinct names", "github.com", "/up/proj/x",
       "&".intercalate ((List.range (n / 8)).map fun i => "k" ++ toString i ++ "=v"),
       some "application/x-www-form-urlencoded"),
     ("form, one name", "github.com", "/up/proj/x", rep (n / 4) "k=v&", some "application/x-www-form-urlencoded"),
     ("form, escapes", "github.com", "/up/proj/x", "k=" ++ rep (n / 3) "%41", some "application/x-www-form-urlencoded"),
     ("multipart", "github.com", "/up/proj/x",
       "--bb\r\n" ++ rep (n / 50) "content-disposition: form-data; name=\"x\"\r\n\r\nv\r\n--bb\r\n",
       some "multipart/form-data"),
     ("multipart, long boundary", "github.com", "/up/proj/x", "--" ++ rep (n / 2) "b" ++ "\r\n" ++ rep (n / 2 - 4) "b",
       some "multipart/form-data"),
     ("GraphQL, many operations", api, "/graphql", "{\"query\":\"" ++ rep (n / 12) "query{a{b}} " ++ "\"}",
       some "application/json"),
     ("GraphQL, deep", api, "/graphql", "{\"query\":\"query" ++ rep (n / 2 - 20) "{" ++ rep (n / 2 - 20) "}" ++ "\"}",
       some "application/json"),
     ("GraphQL, strings", api, "/graphql", "{\"query\":\"query{a(x:" ++ rep (n / 4) "\\\"\\\"" ++ ")}\"}",
       some "application/json"),
     ("GraphQL, comments", api, "/graphql", "{\"query\":\"" ++ rep (n / 4) "#\\r\\n" ++ "query{a}\"}",
       some "application/json"),
     ("push, many updates", "github.com", "/up/proj.git/git-receive-pack",
       Bytes.toStringLossy (pushBody ((List.range (n / 100)).map fun i =>
         (String.ofList (List.replicate 40 '0'), "refs/heads/b" ++ toString i))),
       some "application/x-git-receive-pack-request"),
     ("push, tiny lines", "github.com", "/up/proj.git/git-receive-pack", rep (n / 5) "0005x" ++ "0000",
       some "application/x-git-receive-pack-request"),
     ("fetch, many wants", "github.com", "/up/proj.git/git-upload-pack",
       rep (n / 50) ("0032want " ++ oid ++ "\n") ++ "0000", some "application/x-git-upload-pack-request"),
     ("fetch v2, many arguments", "github.com", "/up/proj.git/git-upload-pack",
       "0014command=fetch\n" ++ rep (n / 50) ("0032want " ++ oid ++ "\n") ++ "0000",
       some "application/x-git-upload-pack-request"),
     ("the platform, a form", "reviews.example", "/api/agent/v1/repos/up/proj/pulls/7/review",
       "&".intercalate ((List.range (n / 8)).map fun i => "k" ++ toString i ++ "=v"),
       some "application/x-www-form-urlencoded")]
  for (n, bound) in [(65536, 250), (2097152, 2000)] do
    for (name, host, path, body, ct) in shapes n do
      let t0 ← IO.monoMsNow
      let decided ← IO.lazyPure fun _ =>
        match choose rr rt "POST" host path body ct with
        | .ok _ => true
        | .error _ => false
      let ms := (← IO.monoMsNow) - t0
      check s!"{name}, {n} bytes: decided in {ms} ms" (decided && ms < bound)
  -- Reading: the bytes arrive a few at a time, and the decoder is asked as they do.
  let feed (data : Bytes) (piece : Nat) : IO Net.Stream := do
    let pos ← IO.mkRef 0
    pure { read := fun _ => do
             let p ← pos.get
             let e := min data.size (p + piece)
             pos.set e
             pure (data.extract p e)
           write := fun _ => pure (), close := pure (), describe := "test" }
  for (n, bound) in [(65536, 250), (2097152, 2000)] do
    let chunked := Bytes.ofString (rep (n / 6) "1\r\nx\r\n" ++ "0\r\n\r\n")
    let pkts := Bytes.ofString (rep (n / 5) "0005x")
    for (name, data, framing, decoder, piece) in [
        ("chunked JSON, 1-byte chunks, 32-byte reads", chunked, Http.Framing.chunked,
          Wire.Decoder.pure Wire.jsonDecoder, 32),
        ("chunked JSON, 1-byte chunks, 64 KiB reads", chunked, .chunked, .pure Wire.jsonDecoder, 65536),
        ("push without a flush, 16-byte reads", pkts, .length pkts.size, .pure Wire.gitReceivePackDecoder, 16),
        ("push without a flush, 512-byte reads", pkts, .length pkts.size,
          .pure Wire.gitReceivePackDecoder, 512)] do
      let stream ← feed data piece
      let t0 ← IO.monoMsNow
      let _ ← Proxy.readBodyPrefix stream framing decoder ByteArray.empty n
      let ms := (← IO.monoMsNow) - t0
      check s!"{name}, {n} bytes: read in {ms} ms" (ms < bound)

end KleisTests
