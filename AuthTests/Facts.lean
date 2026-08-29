import AuthTests.Harness

/-! # Facts and routes -/

namespace AuthTests

open Auth LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

private def render (f : Facts.Fact) : String := Builder.Predicate.print f.predicate

def factsTests : IO Unit := do
  group "primitive facts"
  let request : Model.Request := {
    method := "POST", scheme := "https", host := "github.com", port := 443
    path := "/chrisflav/auth.git/git-receive-pack"
    segments := #["chrisflav", "auth.git", "git-receive-pack"]
    query := #[("service", "git-upload-pack")]
    headers := #[("host", "github.com"), ("content-type", "application/json")]
    bodyPrefix := ByteArray.empty, bodyComplete := true, bodySize := some 12 }
  let facts := (Facts.ofRequest request).map render
  check "method" (facts.contains "request_method(\"POST\")")
  check "host" (facts.contains "request_host(\"github.com\")")
  check "each segment, indexed" (facts.contains "request_segment(1, \"auth.git\")")
  check "headers" (facts.contains "request_header(\"content-type\", \"application/json\")")
  check "query" (facts.contains "request_query(\"service\", \"git-upload-pack\")")
  check "size" (facts.contains "request_size(12)")

  group "body flattening"
  -- One fact per scalar, keyed by its path: this is what lets a rule quantify
  -- over an array, which datalog cannot otherwise do.
  let body : Value := .map [
    (.str "base", .str "main"),
    (.str "updates", .array [
      .map [(.str "ref", .str "refs/heads/a")],
      .map [(.str "ref", .str "refs/heads/b")]])]
  let bodyFacts := (Facts.flatten "body" body 100).map render
  check "a scalar at the top" (bodyFacts.contains "body([\"base\"], \"main\")")
  check "the first element" (bodyFacts.contains "body([\"updates\", 0, \"ref\"], \"refs/heads/a\")")
  check "the second element" (bodyFacts.contains "body([\"updates\", 1, \"ref\"], \"refs/heads/b\")")
  -- Containers are described, not duplicated: emitting a fact per subtree
  -- would repeat every scalar once per ancestor.
  check "the container's shape" (bodyFacts.contains "body_kind([\"updates\"], \"array\")")
  check "the container's length" (bodyFacts.contains "body_len([\"updates\"], 2)")
  check "and it says it was not truncated" (bodyFacts.contains "body_truncated(false)")
  let truncated := (Facts.flatten "body" body 1).map render
  checkEq "past the cap, nothing but the flag" truncated ["body_truncated(true)"]

  group "route patterns"
  match Facts.Pattern.parse "POST github.com /{owner}/{repo%.git}/git-receive-pack" with
  | .error e => check "a pattern parses" false e
  | .ok p => do
    check "a pattern parses" true
    match p.match? request with
    | none => check "it matches the request" false
    | some env => do
      check "it matches the request" true
      checkEq "the owner is captured"
        ((env.lookup "owner").map Builder.Term.print) (some "\"chrisflav\"")
      -- The whole reason routes exist: datalog cannot compute `auth` from
      -- `auth.git` in a rule head.
      checkEq "the suffix is stripped"
        ((env.lookup "repo").map Builder.Term.print) (some "\"auth\"")
  match Facts.Pattern.parse "GET api.github.com /repos/{o}/{r}/pulls/{n:int}/merge" with
  | .error e => check "a typed pattern parses" false e
  | .ok p => do
    let numbered : Model.Request := { request with
      method := "GET", host := "api.github.com"
      segments := #["repos", "a", "b", "pulls", "7", "merge"] }
    match p.match? numbered with
    | none => check "a typed capture matches" false
    | some env =>
      checkEq "and is an integer" ((env.lookup "n").map Builder.Term.print) (some "7")
    -- A segment that is not a number must not match a typed capture.
    let notANumber := { numbered with segments := #["repos", "a", "b", "pulls", "x", "merge"] }
    check "a non-numeric segment does not match" (p.match? notANumber).isNone
  match Facts.Pattern.parse "* * /{rest*}" with
  | .error e => check "a rest pattern parses" false e
  | .ok p =>
    match p.match? request with
    | some env =>
      checkEq "it swallows the tail" ((env.lookup "rest").map Builder.Term.print)
        (some "\"chrisflav/auth.git/git-receive-pack\"")
    | none => check "a rest pattern matches" false
  check "a placeholder must be a whole segment"
    (Facts.Pattern.parse "GET x.com /a{b}c").toOption.isNone

  group "route emission"
  let route : Facts.Route := {
    pattern := (Facts.Pattern.parse "POST github.com /{owner}/{repo%.git}/git-receive-pack").toOption.get!
    captures := []
    emit := [] }
  check "a route with no emissions produces none"
    ((route.apply request none).getD [] |>.isEmpty)
  check "a route that does not match produces nothing"
    (route.apply { request with method := "GET" } none).isNone

end AuthTests
