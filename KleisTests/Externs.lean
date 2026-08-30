import KleisTests.Harness

/-! # Extern functions -/

namespace KleisTests

open Kleis LeanBiscuit
open LeanBiscuit.Datalog (Value)

/-- Call an extern by name. -/
private def call (name : String) (left : Value) (right : Option Value) : Except String Value :=
  match (Policy.standard.find? fun (n, _) => n == name) with
  | some (_, f) => f left right
  | none => throw s!"no extern named {name}"

private def isTrue (r : Except String Value) : Bool :=
  match r with | .ok (.bool true) => true | _ => false

private def isFalse (r : Except String Value) : Bool :=
  match r with | .ok (.bool false) => true | _ => false

def externTests : IO Unit := do
  group "glob"
  check "a star matches within a segment"
    (isTrue (call "glob" (.str "refs/heads/dev/x") (some (.str "refs/heads/dev/*"))))
  -- A policy author writing one star means one level.
  check "a star does not cross a separator"
    (isFalse (call "glob" (.str "refs/heads/dev/a/b") (some (.str "refs/heads/dev/*"))))
  check "a double star does"
    (isTrue (call "glob" (.str "refs/heads/dev/a/b") (some (.str "refs/heads/dev/**"))))
  check "a question mark matches one character"
    (isTrue (call "glob" (.str "abc") (some (.str "a?c"))))
  check "a non-match is false"
    (isFalse (call "glob" (.str "refs/heads/main") (some (.str "refs/heads/dev/*"))))
  check "glob_any over a set"
    (isTrue (call "glob_any" (.str "refs/heads/dev/x")
      (some (.array [.str "refs/tags/*", .str "refs/heads/dev/*"]))))

  group "cidr_contains"
  check "an address inside an IPv4 block"
    (isTrue (call "cidr_contains" (.str "10.0.0.0/8") (some (.str "10.1.2.3"))))
  check "an address outside it"
    (isFalse (call "cidr_contains" (.str "10.0.0.0/8") (some (.str "11.1.2.3"))))
  check "a /32"
    (isTrue (call "cidr_contains" (.str "192.168.1.5/32") (some (.str "192.168.1.5"))))
  check "an IPv6 block"
    (isTrue (call "cidr_contains" (.str "2001:db8::/32") (some (.str "2001:db8:1::1"))))
  -- Mixing families is a false comparison, not an error.
  check "a v4 address is not in a v6 block"
    (isFalse (call "cidr_contains" (.str "2001:db8::/32") (some (.str "10.0.0.1"))))
  check "a malformed block is an error"
    ((call "cidr_contains" (.str "not-a-block") (some (.str "10.0.0.1"))).toOption.isNone)

  group "semver_satisfies"
  check "caret" (isTrue (call "semver_satisfies" (.str "1.4.2") (some (.str "^1.2.0"))))
  check "caret excludes the next major"
    (isFalse (call "semver_satisfies" (.str "2.0.0") (some (.str "^1.2.0"))))
  check "caret on 0.x pins the minor"
    (isFalse (call "semver_satisfies" (.str "0.3.0") (some (.str "^0.2.0"))))
  check "tilde" (isTrue (call "semver_satisfies" (.str "1.2.9") (some (.str "~1.2.0"))))
  check "tilde excludes the next minor"
    (isFalse (call "semver_satisfies" (.str "1.3.0") (some (.str "~1.2.0"))))
  check "a conjunction"
    (isTrue (call "semver_satisfies" (.str "1.5.0") (some (.str ">=1.2.0, <2.0.0"))))

  group "path_normalize"
  checkEq "dot segments resolve" (Policy.pathNormalize "/a/b/../c") "/a/c"
  checkEq "repeated separators collapse" (Policy.pathNormalize "/a//b") "/a/b"
  -- Climbing above the root stays at the root, which is what servers do and
  -- what a policy comparing a prefix has to assume.
  checkEq "climbing above the root stops there" (Policy.pathNormalize "/../../etc") "/etc"

  group "strings"
  checkEq "strip_suffix"
    ((call "strip_suffix" (.str "kleis.git") (some (.str ".git"))).toOption.map fun v =>
      match v with | .str s => s | _ => "")
    (some "kleis")
  check "starts_with_any"
    (isTrue (call "starts_with_any" (.str "refs/heads/dev/x")
      (some (.array [.str "refs/tags/", .str "refs/heads/dev/"]))))
  checkEq "host_of a URL"
    ((call "host_of" (.str "https://API.github.com:443/x") none).toOption.map fun v =>
      match v with | .str s => s | _ => "")
    (some "api.github.com")

  group "arity"
  check "a unary extern rejects a second argument"
    ((call "lower" (.str "x") (some (.str "y"))).toOption.isNone)
  check "a binary extern rejects a missing one"
    ((call "glob" (.str "x") none).toOption.isNone)

end KleisTests
