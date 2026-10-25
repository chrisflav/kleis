import KleisTests.Harness

/-! # Facts and routes -/

namespace KleisTests

open Kleis LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

private def render (f : Facts.Fact) : String := Builder.Predicate.print f.predicate

def factsTests : IO Unit := do
  group "primitive facts"
  let request : Model.Request := {
    method := "POST", scheme := "https", host := "github.com", port := 443
    path := "/chrisflav/kleis.git/git-receive-pack"
    segments := #["chrisflav", "kleis.git", "git-receive-pack"]
    query := #[("service", "git-upload-pack")]
    headers := #[("host", "github.com"), ("content-type", "application/json")]
    bodyPrefix := ByteArray.empty, bodyComplete := true, bodySize := some 12 }
  let facts := (Facts.ofRequest request).map render
  check "method" (facts.contains "request_method(\"POST\")")
  check "host" (facts.contains "request_host(\"github.com\")")
  check "each segment, indexed" (facts.contains "request_segment(1, \"kleis.git\")")
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
  -- `body` above is 3 scalars and 4 containers: 3 + 2 × 4 = 11 facts.
  check "every fact is charged, containers too"
    ((Facts.flatten "body" body 11).map render |>.contains "body_truncated(false)")
  checkEq "so one fewer is too few" ((Facts.flatten "body" body 10).map render) ["body_truncated(true)"]
  let empties : Value := .array (List.replicate 100 (.array []))
  checkEq "empty containers are not free"
    ((Facts.flatten "body" empties 100).map render) ["body_truncated(true)"]
  let nest (n : Nat) : Value := (List.range n).foldl (fun v _ => .array [v]) (.integer 1)
  check s!"nesting {Facts.maxBodyDepth} deep is read"
    ((Facts.flatten "body" (nest Facts.maxBodyDepth) 1000).map render |>.contains "body_truncated(false)")
  checkEq "one deeper is not" ((Facts.flatten "body" (nest (Facts.maxBodyDepth + 1)) 1000).map render)
    ["body_truncated(true)"]
  checkEq "and a truncated body has no whole-body fact either"
    ((Facts.ofBody empties 100).map render) ["body_truncated(true)"]

  group "reading JSON"
  let deep (n : Nat) : String := String.join (List.replicate n "[") ++ String.join (List.replicate n "]")
  check "nesting within the bound parses" (Json.parse (deep 100) (maxDepth := 100)).toOption.isSome
  check "nesting past it does not" (Json.parse (deep 101) (maxDepth := 100)).toOption.isNone
  check "a million levels is refused, not a stack overflow" (Json.parse (deep 1000000)).toOption.isNone
  let wide := "{" ++ ",".intercalate ((List.range 100000).map fun i => "\"k" ++ toString i ++ "\":1") ++ "}"
  let t0 ← IO.monoMsNow
  let dup ← IO.lazyPure fun _ => (Json.parse wide).toOption.map (·.hasDuplicateKeys)
  let ms := (← IO.monoMsNow) - t0
  check s!"an object of 100 000 keys is read and checked for duplicates in {ms} ms"
    (dup == some false && ms < 2000)
  check "and a duplicate is still found"
    ((Json.parse "{\"a\":1,\"b\":2,\"a\":3}").toOption.map (·.hasDuplicateKeys) == some true)

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
      -- The whole reason routes exist: datalog cannot compute `kleis` from
      -- `kleis.git` in a rule head.
      checkEq "the suffix is stripped"
        ((env.lookup "repo").map Builder.Term.print) (some "\"kleis\"")
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
        (some "\"chrisflav/kleis.git/git-receive-pack\"")
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

end KleisTests
