import Kleis.Facts.Route
import Kleis.Util.Toml
import Kleis.Wire.Registry

/-!
# Service manifests

One file describes one upstream service: which hosts it owns, how its
credential is attached, what its requests *mean*, and which decoder reads its
bodies.  Nothing else in the system knows that GitHub exists.

## Manifests cannot escalate

A manifest contributes facts and rules and nothing else.  A `check` or a
`policy` in a manifest is a load error, not a warning — this is the property
that makes it safe to install a manifest you did not write, and enforcing it at
load time rather than at decision time means a bad manifest cannot be sitting
in a directory waiting for the right request.

Only a grant, which the owner of a credential writes, may `allow`.
-/

namespace Kleis
namespace Service

open LeanBiscuit

/-- Where a credential goes in the outgoing request. -/
inductive InjectKind where
  /-- A header field, whose value is the rendered template. -/
  | header
  /-- A query parameter. -/
  | query
  /-- HTTP basic authentication, the template giving `user:password`. -/
  | basic
  deriving Repr, DecidableEq, Inhabited

/-- One place a credential is written into a request.

A service can need more than one, and can need *different* ones per host: a
GitHub token is `Authorization: Bearer` to the REST API and HTTP basic
authentication to the git endpoints, which is the sort of thing only the real
service tells you.  `hosts` is empty for an injection that applies everywhere. -/
structure Injection where
  /-- Which kind of injection. -/
  kind : InjectKind
  /-- The header field or query parameter name. -/
  name : String
  /-- The value, with `{{secret}}` where the secret goes. -/
  template : String
  /-- The hosts this applies to; empty means all of the credential's. -/
  hosts : List String := []
  deriving Repr, Inhabited

/-- Does this injection apply to a request for this host? -/
def Injection.appliesTo (i : Injection) (host : String) : Bool :=
  i.hosts.isEmpty || i.hosts.any fun h => Facts.hostMatches h host

/-- How this service's credential is obtained and attached. -/
structure CredentialSpec where
  /-- The provider name: `static`, `oauth2`, `github-app`, `exec`. -/
  provider : String
  /-- The only hosts the credential may ever be sent to. -/
  hosts : List String
  /-- Where it goes. -/
  inject : List Injection
  /-- Header fields removed from the client's request before forwarding. -/
  strip : List String
  /-- Provider-specific settings, passed through untouched. -/
  config : Json
  deriving Inhabited

/-- A media type bound to a decoder, optionally only for the requests one
pattern matches.

The pattern is what lets a service whose API is mostly one format carve out an
endpoint that is another wearing the same media type: GitHub's GraphQL endpoint
takes `application/json` like the rest of its API, and only there is the
`query` field a document worth reading.  The first binding that applies wins,
so a narrow one is written above a broad one. -/
structure DecoderBinding where
  /-- The media types this covers. -/
  media : List String
  /-- The decoder's registry name, or `exec:<command>`. -/
  decoder : String
  /-- The requests it is limited to, if it is. -/
  when : Option Facts.Pattern := none
  deriving Repr, Inhabited

/-- A service. -/
structure Manifest where
  /-- The service's name, which is how a grant refers to it. -/
  name : String
  /-- Every host this manifest claims. -/
  hosts : List String
  /-- The interception modes it supports: `rewrite`, `connect`, `transparent`. -/
  modes : List String
  /-- The credential. -/
  credential : CredentialSpec
  /-- Routes, in order; every one that matches contributes its facts. -/
  routes : List Facts.Route
  /-- Facts the manifest asserts unconditionally. -/
  facts : List Builder.Fact
  /-- Rules deriving semantic facts from primitive ones. -/
  rules : List Builder.Rule
  /-- Media types bound to decoders. -/
  decoders : List DecoderBinding
  /-- The decoder for a body whose media type matched nothing. -/
  defaultDecoder : Option String
  /-- The largest number of body facts to emit. -/
  maxBodyFacts : Nat
  /-- The largest body prefix a decoder may be given. -/
  maxDecodePrefix : Nat
  /-- The SHA-256 of the source, hex, recorded in the audit log so a decision
  can be replayed against the manifest that made it. -/
  version : String
  deriving Inhabited

/-- Read the string elements of an array field. -/
private def strings (j : Json) (k : String) : List String :=
  (j.arr? k).filterMap Json.asString?

/-- Read an injection from a table. -/
private def injectionOf (j : Json) : Except String Injection := do
  let kind ← match j.str? "kind" with
    | some "header" => pure InjectKind.header
    | some "query" => pure InjectKind.query
    | some "basic" => pure InjectKind.basic
    | some k => throw s!"unknown injection kind `{k}`"
    | none => throw "an injection needs a `kind`"
  let name ← match j.str? "name" with
    | some n => pure n
    | none => if kind == .basic then pure "authorization" else throw "an injection needs a `name`"
  let template ← match j.str? "template" with
    | some t => pure t
    | none => throw "an injection needs a `template`"
  pure { kind, name := Str.toLowerAscii name, template
         hosts := (strings j "hosts").map Str.toLowerAscii }

/-- Read a route from a table. -/
private def routeOf (j : Json) : Except String Facts.Route := do
  let matchLine ← match j.str? "match" with
    | some m => pure m
    | none => throw "a route needs a `match`"
  let pattern ← Facts.Pattern.parse matchLine
  let captures ← match (j.field? "capture").getD (.obj []) with
    | .obj fields => fields.mapM fun (name, v) => do
      match v.asString? with
      | some s => pure (name, ← Facts.Source.parse s)
      | none => throw s!"the capture `{name}` must be a string"
    | _ => throw "`capture` must be a table"
  -- Every emitted fact is parsed here, once, so that a captured value is
  -- substituted as a term and can never be read as syntax.
  --
  -- The template is parsed inside a `check`, not as a fact: a fact has to be
  -- ground and a template is exactly a fact that is not yet, so the parser
  -- would reject `repository($owner, $repo)` on its own.  A check's query body
  -- is a list of predicates, variables and all, which is what a template is.
  let emit ← (strings j "emit").mapM fun src =>
    let src := Str.stripSuffix (Str.trim src) ";"
    match Parser.parseAuthorizer s!"check if {src};" with
    | .error e => throw s!"in `{src}`: {e}"
    | .ok r =>
      match r.checks with
      | [c] =>
        match c.queries with
        | [q] =>
          if !q.expressions.isEmpty then
            throw s!"a route emits a fact, not an expression: `{src}`"
          else match q.body with
            | [pred] => .ok (Builder.Fact.mk pred)
            | [] => throw s!"`{src}` emits nothing"
            | _ => throw s!"`{src}` emits more than one fact; use separate entries"
        | _ => throw s!"`{src}` is not a single fact"
      | _ => throw s!"`{src}` is not a single fact"
  pure { pattern, captures, emit,
         responseGated := (j.bool? "response_gated").getD false }

/-- Read a decoder binding. -/
private def decoderOf (j : Json) : Except String DecoderBinding := do
  let decoder ← match j.str? "decoder" with
    | some d => pure d
    | none => throw "a decoder binding needs a `decoder`"
  let when ← match j.str? "match" with
    | some m => some <$> Facts.Pattern.parse m
    | none => pure none
  pure { media := (strings j "media").map (fun m => Str.toLowerAscii (Str.trim m)), decoder, when }

/-- Read the manifest's datalog: facts and rules only. -/
private def datalogOf (source : String) : Except String (List Builder.Fact × List Builder.Rule) :=
  match Parser.parseAuthorizer source with
  | .error e => throw s!"in the manifest's datalog: {e}"
  | .ok r =>
    if !r.checks.isEmpty then
      throw "a manifest may not contain a check; only a grant decides authority"
    else if !r.policies.isEmpty then
      throw "a manifest may not contain a policy; only a grant may allow"
    else .ok (r.facts, r.rules)

/-- Read a manifest from TOML source. -/
def Manifest.ofToml (source : String) : Except String Manifest := do
  let j ← Toml.parse source
  let name ← match j.str? "name" with
    | some n => pure n
    | none => throw "a manifest needs a `name`"
  let hosts := (strings j "hosts").map Str.toLowerAscii
  if hosts.isEmpty then throw "a manifest needs at least one host"
  let credJson := (j.field? "credential").getD (.obj [])
  let credential : CredentialSpec := {
    provider := (credJson.str? "provider").getD "static"
    hosts := match strings credJson "hosts" with
      | [] => hosts
      | hs => hs.map Str.toLowerAscii
    inject := ← ((credJson.arr? "inject").mapM injectionOf)
    strip := (strings credJson "strip").map Str.toLowerAscii
    config := credJson
  }
  for h in credential.hosts do
    if !hosts.contains h then
      throw s!"the credential is bound to `{h}`, which the manifest does not claim"
  let routes ← (j.arr? "route").mapM routeOf
  let (facts, rules) ← datalogOf ((j.str? "datalog").getD "")
  let decoders ← (j.arr? "decoder").mapM decoderOf
  pure {
    name, hosts
    modes := match strings j "modes" with
      | [] => ["rewrite", "connect", "transparent"]
      | ms => ms
    credential, routes, facts, rules, decoders
    defaultDecoder := j.str? "default_decoder"
    maxBodyFacts := ((j.int? "max_body_facts").getD 256).toNat
    maxDecodePrefix := ((j.int? "max_decode_prefix").getD 65536).toNat
    version := Bytes.toHex (Sha256.hash (Bytes.ofString source))
  }

/-- Does this manifest claim the host? -/
def Manifest.claims (m : Manifest) (host : String) : Bool :=
  m.hosts.any fun h => Facts.hostMatches h host

/-- May the credential be sent to this host?

The check every redirect goes back through.  A host the manifest claims but the
credential is not bound to is proxied without the credential, not refused: the
request is still the client's to make, it just does not get to spend anything. -/
def Manifest.mayCredentialReach (m : Manifest) (host : String) : Bool :=
  m.credential.hosts.any fun h => Facts.hostMatches h host

/-- The decoder to use for a body, from its media type. -/
def Manifest.decoderFor (m : Manifest) (contentType : Option String)
    (request : Option Model.Request := none) : Wire.Decoder :=
  let bare := (contentType.getD "").splitOn ";" |>.headD "" |> Str.trim |> Str.toLowerAscii
  -- A binding limited to some requests applies only when the request is known
  -- and matches; without the request, only the unconditional ones are candidates.
  let applies (b : DecoderBinding) : Bool :=
    b.media.contains bare && match b.when, request with
      | none, _ => true
      | some p, some r => (p.match? r).isSome
      | some _, none => false
  let named := (m.decoders.find? applies).map (·.decoder)
  let name := named.orElse fun _ =>
    (Wire.byMedia? bare).map (·.name) |>.orElse fun _ => m.defaultDecoder
  match name with
  | none => .opaque
  | some n =>
    if n.startsWith "exec:" then
      match ((Str.stripPrefix n "exec:").splitOn " ").filter (!·.isEmpty) with
      | [] => .opaque
      | cmd :: args => .exec cmd args
    else match Wire.byName? n with
      | some d => .pure d
      | none => .opaque

/-- The facts and rules a manifest contributes to an authorizer, given a
request and its decoded body. -/
def Manifest.contribute (m : Manifest) (r : Model.Request) (body : Option LeanBiscuit.Datalog.Value) :
    List Builder.Fact :=
  m.facts ++ (m.routes.flatMap fun rt => (rt.apply r body).getD [])

/-- Does any route matching this request want the response checked? -/
def Manifest.gatesResponse (m : Manifest) (r : Model.Request)
    (body : Option LeanBiscuit.Datalog.Value) : Bool :=
  m.routes.any fun rt => rt.responseGated && (rt.apply r body).isSome

end Service
end Kleis
