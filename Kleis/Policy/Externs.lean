import Kleis.Facts.Primitive

/-!
# Extern functions

The host functions datalog may call, as `$x.extern::name($y)`.

Two constraints shape this list.  First, an extern is a *filter*: it is
evaluated inside an expression, and an expression only decides whether a rule
fires, so an extern can never bind a variable or mint a term for a rule head —
that is what routes are for.  Second, the set is fixed at build time, which is
precisely why every function here has to be service-independent.  A manifest
wanting a GitHub-shaped extern is a review comment, not a patch: it should be a
route or a rule.

So what is here is the small set of things datalog genuinely cannot say: glob
matching, address containment, version ranges, path normalisation, and a few
string operations whose absence would otherwise push service knowledge into
Lean.
-/

namespace Kleis
namespace Policy

open LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey ExternFunc Externs)

/-- Demand a string argument. -/
private def asStr (name : String) : Value → Except String String
  | .str s => .ok s
  | v => throw s!"extern::{name} expects a string, got {repr v}"

/-- Demand the right-hand argument of a binary call. -/
private def rhs (name : String) : Option Value → Except String Value
  | some v => .ok v
  | none => throw s!"extern::{name} is binary and was called with one argument"

/-! ## Glob matching -/

/-- Match a glob against a subject.

`*` matches within one path segment, `**` matches across segments, and `?`
matches one character.  The distinction matters: a rule allowing
`refs/heads/dev/*` should not thereby allow `refs/heads/dev/a/b`, because a
policy author writing one star is thinking of one level. -/
partial def globMatch (pat subj : List Char) : Bool :=
  match pat, subj with
  | [], [] => true
  | [], _ => false
  | '*' :: '*' :: p, s =>
    -- `**` consumes anything, including separators.
    globMatch p s || (match s with | [] => false | _ :: s' => globMatch ('*' :: '*' :: p) s')
  | '*' :: p, s =>
    globMatch p s ||
      (match s with
       | [] => false
       | c :: s' => if c == '/' then false else globMatch ('*' :: p) s')
  | '?' :: p, _ :: s => globMatch p s
  | '?' :: _, [] => false
  | c :: p, d :: s => c == d && globMatch p s
  | _ :: _, [] => false

/-! ## Addresses -/

/-- Parse a dotted-quad IPv4 address into its 32 bits. -/
private def parseIPv4? (s : String) : Option Nat := do
  let parts := s.splitOn "."
  if parts.length != 4 then none else
    parts.foldlM (init := 0) fun acc p => do
      let n ← p.toNat?
      if n > 255 then none else some (acc * 256 + n)

/-- Parse an IPv6 address into its 128 bits, `::` included. -/
private def parseIPv6? (s : String) : Option Nat := do
  let (headText, tailText) ← match Str.splitOnce? s "::" with
    | some (a, b) => some (a, some b)
    | none => some (s, none)
  let groups (t : String) : Option (List Nat) :=
    if t.isEmpty then some []
    else (t.splitOn ":").mapM fun g =>
      if g.isEmpty || g.length > 4 then none else Str.ofHex? g
  let head ← groups headText
  match tailText with
  | none => if head.length != 8 then none else
      some (head.foldl (fun acc g => acc * 65536 + g) 0)
  | some t => do
    let tail ← groups t
    let missing := 8 - (head.length + tail.length)
    if head.length + tail.length > 8 then none else
      let all := head ++ List.replicate missing 0 ++ tail
      some (all.foldl (fun acc g => acc * 65536 + g) 0)

/-- Is the address inside the network? -/
private def cidrContains (cidr addr : String) : Except String Bool := do
  let (net, bitsText) ← match Str.splitOnce? cidr "/" with
    | some p => pure p
    | none => throw s!"`{cidr}` is not a CIDR block"
  let bits ← match bitsText.toNat? with
    | some b => pure b
    | none => throw s!"`{bitsText}` is not a prefix length"
  match parseIPv4? net, parseIPv4? addr with
  | some n, some a =>
    if bits > 32 then throw "an IPv4 prefix length is at most 32"
    else
      let shift := 32 - bits
      pure (n >>> shift == a >>> shift)
  | _, _ =>
    match parseIPv6? net, parseIPv6? addr with
    | some n, some a =>
      if bits > 128 then throw "an IPv6 prefix length is at most 128"
      else
        let shift := 128 - bits
        pure (n >>> shift == a >>> shift)
    | _, _ =>
      -- Mixing families is a false comparison, not an error: a v4 client
      -- address simply is not in a v6 block.
      pure false

/-! ## Versions -/

/-- Split a semantic version into its numeric parts, ignoring any pre-release
or build metadata. -/
private def semverParts (s : String) : List Nat :=
  let core := ((s.splitOn "+").headD s).splitOn "-" |>.headD s
  let core := Str.stripPrefix (Str.trim core) "v"
  (core.splitOn ".").map fun p => (p.toNat?).getD 0

/-- Compare two versions part by part, shorter padded with zeros. -/
private def semverCompare (a b : String) : Ordering :=
  let pa := semverParts a
  let pb := semverParts b
  let n := max pa.length pb.length
  let nth (l : List Nat) (i : Nat) := (l[i]?).getD 0
  Id.run do
    for i in [0:n] do
      match Ord.compare (nth pa i) (nth pb i) with
      | .eq => pure ()
      | o => return o
    return .eq

/-- Does a version satisfy a range?

Supports `=`, `>`, `>=`, `<`, `<=`, `^` and `~`, and a comma-separated
conjunction of them.  Deliberately not the whole of the npm range grammar:
a policy that needs more than this is expressing something a version range
should not be deciding. -/
private def semverSatisfies (version range : String) : Except String Bool := do
  let one (r : String) : Except String Bool := do
    let r := Str.trim r
    if r.isEmpty || r == "*" then pure true
    else if r.startsWith ">=" then
      pure (semverCompare version (Str.stripPrefix r ">=") != .lt)
    else if r.startsWith "<=" then
      pure (semverCompare version (Str.stripPrefix r "<=") != .gt)
    else if r.startsWith ">" then
      pure (semverCompare version (Str.stripPrefix r ">") == .gt)
    else if r.startsWith "<" then
      pure (semverCompare version (Str.stripPrefix r "<") == .lt)
    else if r.startsWith "^" then
      let base := Str.stripPrefix r "^"
      let parts := semverParts base
      let upper := match parts with
        | 0 :: minor :: _ => s!"0.{minor + 1}.0"
        | major :: _ => s!"{major + 1}.0.0"
        | [] => "0.0.0"
      pure (semverCompare version base != .lt && semverCompare version upper == .lt)
    else if r.startsWith "~" then
      let base := Str.stripPrefix r "~"
      let parts := semverParts base
      let upper := match parts with
        | major :: minor :: _ => s!"{major}.{minor + 1}.0"
        | [major] => s!"{major + 1}.0.0"
        | [] => "0.0.0"
      pure (semverCompare version base != .lt && semverCompare version upper == .lt)
    else pure (semverCompare version (Str.stripPrefix r "=") == .eq)
  let parts := (range.splitOn ",").filter (!·.trimAscii.toString.isEmpty)
  parts.foldlM (init := true) fun acc r => do pure (acc && (← one r))

/-! ## Paths -/

/-- Resolve `.` and `..` and collapse repeated separators.

A path that climbs above its root stays at the root, which is what every
server does and what a policy comparing against a prefix has to assume. -/
def pathNormalize (p : String) : String :=
  let absolute := p.startsWith "/"
  let out := (p.splitOn "/").foldl (init := ([] : List String)) fun acc seg =>
    if seg.isEmpty || seg == "." then acc
    else if seg == ".." then acc.dropLast
    else acc ++ [seg]
  (if absolute then "/" else "") ++ "/".intercalate out

/-! ## The table -/

/-- A unary extern, wrapped so that a binary call to it is an error rather
than a silently ignored argument. -/
private def unary (name : String) (f : Value → Except String Value) : String × ExternFunc :=
  (name, fun v r => match r with
    | some _ => throw s!"extern::{name} is unary and was called with two arguments"
    | none => f v)

/-- A binary extern. -/
private def binary (name : String) (f : Value → Value → Except String Value) :
    String × ExternFunc :=
  (name, fun l r => do f l (← rhs name r))

/-- Every extern the authorizer offers. -/
def standard : Externs :=
  [ unary "lower" (fun v => do pure (.str (Str.toLowerAscii (← asStr "lower" v)))),
    unary "upper" (fun v => do pure (.str ((← asStr "upper" v).toUpper))),
    unary "trim" (fun v => do pure (.str (Str.trim (← asStr "trim" v)))),
    unary "path_normalize" (fun v => do
      pure (.str (pathNormalize (← asStr "path_normalize" v)))),
    unary "sha256" (fun v => do
      match v with
      | .bytes b => pure (.bytes (Sha256.hash b))
      | .str s => pure (.bytes (Sha256.hash (Bytes.ofString s)))
      | _ => throw "extern::sha256 expects a string or a byte string"),
    unary "hex" (fun v => do
      match v with
      | .bytes b => pure (.str (Bytes.toHex b))
      | _ => throw "extern::hex expects a byte string"),
    unary "host_of" (fun v => do
      let s ← asStr "host_of" v
      let rest := if s.startsWith "https://" then Str.stripPrefix s "https://"
                  else if s.startsWith "http://" then Str.stripPrefix s "http://"
                  else s
      let authority := (rest.splitOn "/").headD rest
      pure (.str (Str.toLowerAscii ((authority.splitOn ":").headD authority)))),
    binary "glob" (fun l r => do
      pure (.bool (globMatch (← asStr "glob" r).toList (← asStr "glob" l).toList))),
    binary "glob_any" (fun l r => do
      let subj := (← asStr "glob_any" l).toList
      match r with
      | .array pats | .set pats =>
        pats.foldlM (init := Value.bool false) fun acc p => do
          match acc with
          | .bool true => pure (.bool true)
          | _ => pure (.bool (globMatch (← asStr "glob_any" p).toList subj))
      | _ => throw "extern::glob_any expects an array or a set of patterns"),
    binary "starts_with_any" (fun l r => do
      let subj ← asStr "starts_with_any" l
      match r with
      | .array pats | .set pats =>
        pats.foldlM (init := Value.bool false) fun acc p => do
          match acc with
          | .bool true => pure (.bool true)
          | _ => pure (.bool (subj.startsWith (← asStr "starts_with_any" p)))
      | _ => throw "extern::starts_with_any expects an array or a set of prefixes"),
    binary "strip_prefix" (fun l r => do
      pure (.str (Str.stripPrefix (← asStr "strip_prefix" l) (← asStr "strip_prefix" r)))),
    binary "strip_suffix" (fun l r => do
      pure (.str (Str.stripSuffix (← asStr "strip_suffix" l) (← asStr "strip_suffix" r)))),
    binary "cidr_contains" (fun l r => do
      pure (.bool (← cidrContains (← asStr "cidr_contains" l) (← asStr "cidr_contains" r)))),
    binary "semver_satisfies" (fun l r => do
      pure (.bool (← semverSatisfies (← asStr "semver_satisfies" l)
        (← asStr "semver_satisfies" r)))) ]

end Policy
end Kleis
