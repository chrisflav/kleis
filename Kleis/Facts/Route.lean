import Kleis.Facts.Primitive
import LeanBiscuit

/-!
# Routes

Datalog can filter but it cannot compute a new term in a rule head: an extern
evaluates inside an expression, and an expression only decides whether a rule
fires.  So `kleis.git ↦ kleis` cannot be written as a rule.  Routes exist for
exactly that gap, and are the only bespoke syntax in the system.

```toml
[[route]]
match = "POST github.com /{owner}/{repo%.git}/git-receive-pack"
emit  = ['operation("push")', 'repository($owner, $repo)']
```

## Why the emitted facts are parsed, not printed

A capture holds whatever the client sent.  Substituting it into the *text* of
`repository($owner, $repo)` and parsing the result would be a datalog injection
hole the width of a repository name: a request for `/a")%20or%20admin("/x.git`
would emit whatever its author liked.

So the template is parsed once, at load time, into a fact with variables in it,
and a capture is substituted as a *term* into the parsed structure.  A captured
value can therefore never be read as syntax, whatever it contains.  This is the
same reason a database interface binds parameters rather than pasting them.
-/

namespace Kleis
namespace Facts

open LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

/-- How a captured string is turned into a term. -/
inductive CaptureKind where
  /-- A string, the default. -/
  | str
  /-- A decimal integer; a segment that is not one does not match. -/
  | int
  /-- An RFC 3339 timestamp; a segment that is not one does not match. -/
  | date
  deriving Repr, DecidableEq, Inhabited

/-- One element of a path pattern. -/
inductive SegPat where
  /-- A segment that must appear literally. -/
  | literal (text : String)
  /-- A segment captured under a name, optionally typed, optionally with a
  suffix stripped before it is bound. -/
  | capture (name : String) (kind : CaptureKind) (strip : Option String)
  /-- Every remaining segment, bound as one `/`-joined string. -/
  | rest (name : String)
  deriving Repr, Inhabited

/-- A parsed `match` line. -/
structure Pattern where
  /-- The methods this matches; empty means any. -/
  methods : List String
  /-- The host, `*`, or a `*.suffix` wildcard. -/
  host : String
  /-- The path pattern. -/
  segments : List SegPat
  deriving Repr, Inhabited

/-- Parse the inside of a `{…}` placeholder. -/
private def parsePlaceholder (inner : String) : Except String SegPat := do
  if inner.endsWith "*" then
    let name := Str.stripSuffix inner "*"
    if name.isEmpty then throw "a `{*}` capture needs a name" else pure (.rest name)
  else
    let (head, strip) := match Str.splitOnce? inner "%" with
      | some (h, s) => (h, some s)
      | none => (inner, none)
    let (name, kind) ← match Str.splitOnce? head ":" with
      | some (n, "int") => pure (n, CaptureKind.int)
      | some (n, "date") => pure (n, CaptureKind.date)
      | some (_, t) => throw s!"unknown capture type `{t}`"
      | none => pure (head, CaptureKind.str)
    if name.isEmpty then throw "a capture needs a name"
    pure (.capture name kind strip)

/-- Parse one path segment of a pattern. -/
private def parseSegPat (s : String) : Except String SegPat :=
  if s.startsWith "{" && s.endsWith "}" then
    parsePlaceholder ((s.drop 1).dropEnd 1).toString
  else if s.any (fun c => c == '{' || c == '}') then
    throw s!"a placeholder must be a whole path segment: `{s}`"
  else .ok (.literal s)

/-- Parse a `match` line: `METHOD[|METHOD…] HOST /path/pattern`.

`*` in the method or host position means any.  A host may also be written
`*.example.com`, which matches a subdomain but not the bare name — the bare
name has to be listed if it is meant, because a credential bound to a wildcard
that silently included the apex would be a surprise in the wrong direction. -/
def Pattern.parse (line : String) : Except String Pattern := do
  match (line.splitOn " ").filter (!·.isEmpty) with
  | [methods, host, path] =>
    let methods := if methods == "*" then []
      else (methods.splitOn "|").map fun m => (Str.trim m).toUpper
    let segments ← ((Str.pathOnly path).splitOn "/").filter (!·.isEmpty) |>.mapM parseSegPat
    pure { methods, host := Str.toLowerAscii host, segments }
  | _ => throw s!"a match line is `METHOD HOST /path`, not `{line}`"

/-- Does a host pattern accept this host? -/
def hostMatches (pattern host : String) : Bool :=
  if pattern == "*" then true
  else if pattern.startsWith "*." then
    let suffix := Str.stripPrefix pattern "*"
    host.endsWith suffix && host.length > suffix.length
  else pattern == host

/-- Turn a captured string into a term, or fail the match. -/
private def bindCapture (kind : CaptureKind) (strip : Option String) (raw : String) :
    Option Builder.Term :=
  let raw := match strip with
    | some s => Str.stripSuffix raw s
    | none => raw
  match kind with
  | .str => some (.str raw)
  | .int => raw.toInt?.map Builder.Term.integer
  | .date => (Time.parseRfc3339 raw).map fun t =>
      Builder.Term.date (if t < 0 then 0 else t.toNat)

/-- Match a path pattern against the request's segments. -/
private def matchSegments : List SegPat → List String → Option (List (String × Builder.Term))
  | [], [] => some []
  | [], _ :: _ => none
  | .rest name :: _, rest => some [(name, .str ("/".intercalate rest))]
  | _ :: _, [] => none
  | .literal l :: ps, s :: ss => if l == s then matchSegments ps ss else none
  | .capture name kind strip :: ps, s :: ss => do
    let t ← bindCapture kind strip s
    let more ← matchSegments ps ss
    pure ((name, t) :: more)

/-- Match a pattern against a request, returning the captures. -/
def Pattern.match? (p : Pattern) (r : Model.Request) :
    Option (List (String × Builder.Term)) :=
  if !p.methods.isEmpty && !p.methods.contains r.method then none
  else if !hostMatches p.host r.host then none
  else matchSegments p.segments r.segments.toList

/-! ## Extra captures -/

/-- Where a capture that is not a path segment comes from. -/
inductive Source where
  /-- A request header, by lowercased name. -/
  | header (name : String)
  /-- A query parameter. -/
  | query (name : String)
  /-- A path into the decoded body, written with dots: `updates.0.ref`. -/
  | body (path : List String)
  /-- The request method. -/
  | method
  /-- The request host. -/
  | host
  /-- The whole path. -/
  | path
  deriving Repr, Inhabited

/-- Parse a capture source: `header:x`, `query:x`, `body:a.0.b`, `method`,
`host`, `path`. -/
def Source.parse (s : String) : Except String Source :=
  match Str.splitOnce? s ":" with
  | some ("header", n) => .ok (.header (Str.toLowerAscii n))
  | some ("query", n) => .ok (.query n)
  | some ("body", p) => .ok (.body ((p.splitOn ".").filter (!·.isEmpty)))
  | some (k, _) => throw s!"unknown capture source `{k}`"
  | none =>
    match s with
    | "method" => .ok .method
    | "host" => .ok .host
    | "path" => .ok .path
    | _ => throw s!"unknown capture source `{s}`"

/-- Follow a dotted path into a decoded value. -/
private def lookup? (v : Value) : List String → Option Value
  | [] => some v
  | key :: rest =>
    match v with
    | .map entries =>
      let hit := entries.find? fun (k, _) => match k with
        | .str s => s == key
        | .integer i => toString i == key
      hit.bind fun (_, sub) => lookup? sub rest
    | .array l => key.toNat?.bind fun i => (l[i]?).bind fun sub => lookup? sub rest
    | _ => none

/-- Resolve a capture source against a request and its decoded body. -/
def Source.resolve (s : Source) (r : Model.Request) (body : Option Value) :
    Option Builder.Term :=
  match s with
  | .header n => (Http.Headers.find? r.headers n).map Builder.Term.str
  | .query n => ((Array.find? (fun (k, _) => k == n) r.query)).map fun (_, v) => .str v
  | .body p => do
    let b ← body
    let v ← lookup? b p
    pure (ofValue v)
  | .method => some (.str r.method)
  | .host => some (.str r.host)
  | .path => some (.str r.path)

/-! ## Substitution -/

mutual

/-- Replace every variable by its captured term.  A variable with no capture is
left in place, and the caller drops the fact rather than emitting a fact with a
free variable in it. -/
def substTerm (env : List (String × Builder.Term)) : Builder.Term → Builder.Term
  | .variable n => match env.find? (fun (k, _) => k == n) with
    | some (_, t) => t
    | none => .variable n
  | .set l => .set (Builder.mkSet (substList env l))
  | .array l => .array (substList env l)
  | .map entries => .map (Builder.mkMap (substEntries env entries))
  | t => t

/-- Substitute in a list of terms. -/
def substList (env : List (String × Builder.Term)) : List Builder.Term → List Builder.Term
  | [] => []
  | x :: xs => substTerm env x :: substList env xs

/-- Substitute in a list of map entries. -/
def substEntries (env : List (String × Builder.Term)) :
    List (Builder.MapKey × Builder.Term) → List (Builder.MapKey × Builder.Term)
  | [] => []
  | (k, v) :: xs => (k, substTerm env v) :: substEntries env xs

end

mutual

/-- Is this term free of variables? -/
def isGround : Builder.Term → Bool
  | .variable _ => false
  | .set l => isGroundList l
  | .array l => isGroundList l
  | .map entries => isGroundEntries entries
  | _ => true

/-- Are all of these terms ground? -/
def isGroundList : List Builder.Term → Bool
  | [] => true
  | x :: xs => isGround x && isGroundList xs

/-- Are all of these entries' values ground? -/
def isGroundEntries : List (Builder.MapKey × Builder.Term) → Bool
  | [] => true
  | (_, v) :: xs => isGround v && isGroundEntries xs

end

/-- A route: a pattern, extra captures, and the facts to emit. -/
structure Route where
  /-- The `match` line, parsed. -/
  pattern : Pattern
  /-- Captures beyond the path segments. -/
  captures : List (String × Source)
  /-- The facts to emit, parsed, with variables where captures go. -/
  emit : List Fact
  /-- Whether a match means the response must be buffered and checked. -/
  responseGated : Bool := false
  deriving Inhabited

/-- Apply a route to a request.  Returns the facts it emits, with every capture
substituted; a fact still holding a free variable is dropped, because a
capture that did not resolve must not silently become a wildcard. -/
def Route.apply (rt : Route) (r : Model.Request) (body : Option Value) :
    Option (List Fact) := do
  let pathEnv ← rt.pattern.match? r
  let extraEnv := rt.captures.filterMap fun (name, src) =>
    (src.resolve r body).map fun t => (name, t)
  let env := pathEnv ++ extraEnv
  pure <| rt.emit.filterMap fun f =>
    let terms := substList env f.predicate.terms
    if isGroundList terms then some (fact f.predicate.name terms) else none

end Facts
end Kleis
