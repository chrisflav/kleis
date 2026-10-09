import Kleis.Util.Toml
import Kleis.Dirs
import Kleis.Store
import Kleis.Policy.Grant

/-!
# Configuration

`$KLEIS_HOME/config/config.toml`, or the defaults below, which are chosen so
that a daemon started with no configuration at all does something safe and
useful: listen on the loopback, accept both interception modes, and refuse
anything it has no manifest for.
-/

namespace Kleis

/-- How the proxy expects to be reached. -/
inductive Mode where
  /-- `CONNECT` with interception: real URLs, needs the CA installed. -/
  | connect
  /-- Plain HTTP on the loopback with the origin in the path: no TLS server
  needed, and what to use before the CA is set up. -/
  | rewrite
  /-- Both, chosen per request by its shape. -/
  | both
  deriving Repr, DecidableEq, Inhabited

/-- Does this mode accept `CONNECT`? -/
def Mode.intercepts : Mode → Bool
  | .connect | .both => true
  | .rewrite => false

/-- Does this mode accept rewritten origin-form requests? -/
def Mode.rewrites : Mode → Bool
  | .rewrite | .both => true
  | .connect => false

/-- A program allowed to ask the daemon for tokens.

An issuer is how a system that hands out work — a CI runner, an agent
orchestrator — gets a token per job without holding the root key.  What it may
put in one is bounded here, by the owner, and not by the issuer: the grants it
may name, the facts it may add, and how long the result may live.

The facts are the part to be careful with.  A fact in a token's authority block
is believed by every grant, so an issuer allowed to write `repository(…)` could
satisfy any grant's repository check with it.  `facts` is therefore a list of
predicate *names* the issuer may use — `task_*` and the like — and the names the
proxy and the shipped manifests give meaning to are refused whatever it says
(`Token.reservedPredicates`). -/
structure Issuer where
  /-- The name its credential carries as `issuer(name)`. -/
  name : String
  /-- Grant names, or `prefix*` patterns, its tokens may claim. -/
  grants : List String
  /-- Predicate names, or `prefix*` patterns, its tokens may carry as facts. -/
  facts : List String
  /-- The longest a token it issues may live, in seconds.  A grant's own
  `max_lifetime` still applies. -/
  maxTtl : Nat
  /-- Where kleisd keeps this issuer's own credential, if it should: minted at
  startup when the file is missing, unreadable, revoked or within a quarter of its
  lifetime of expiring, and left alone otherwise.  For a deployment where the
  issuer runs beside kleisd and is handed the file, rather than a person running
  `kleis issuer token` and pasting the result somewhere. -/
  tokenFile : Option String := none
  /-- How long a credential written to `tokenFile` lives, in seconds. -/
  tokenTtl : Nat := 365 * 86400
  deriving Repr, Inhabited

/-- Does a name match a list of names and `prefix*` patterns? -/
def namePatternsMatch (patterns : List String) (name : String) : Bool :=
  patterns.any fun p =>
    if p.endsWith "*" then name.startsWith (Str.stripSuffix p "*") else p == name

/-- May this issuer claim a grant? -/
def Issuer.mayClaim (i : Issuer) (grant : String) : Bool := namePatternsMatch i.grants grant

/-- May this issuer add a fact with this predicate? -/
def Issuer.mayState (i : Issuer) (predicate : String) : Bool :=
  namePatternsMatch i.facts predicate

/-- Everything the daemon reads at startup. -/
structure Config where
  /-- The address to listen on.  The loopback by default: a credential proxy
  reachable from the network is a credential server. -/
  listenHost : String := "127.0.0.1"
  /-- The port. -/
  listenPort : UInt16 := 8080
  /-- Which interception modes to accept. -/
  mode : Mode := .both
  /-- A trust store for verifying origins, or empty for the system one. -/
  upstreamCaFile : String := ""
  /-- The largest header block accepted from a client. -/
  maxHeadSize : Nat := 65536
  /-- The largest body prefix handed to a decoder, unless a manifest says
  otherwise. -/
  maxDecodePrefix : Nat := 65536
  /-- The largest number of body facts, unless a manifest says otherwise. -/
  maxBodyFacts : Nat := 256
  /-- How many requests one connection may carry before it is closed. -/
  maxRequestsPerConnection : Nat := 100
  /-- How long an idle connection to an origin is kept for reuse, in seconds.
  Zero turns reuse off. -/
  upstreamIdleSeconds : Nat := 30
  /-- Whether to write an audit record for every decision. -/
  audit : Bool := true
  /-- Hosts no manifest claims that a bearer may still reach through this
  proxy, as host patterns (`*`, `*.example.com`, `example.com`).

  Empty by default, which is the design's stance: a credential proxy, not an
  egress path.  It is here for the deployment where every program in a sandbox
  is pointed at the proxy with `HTTPS_PROXY` — a package manager, a toolchain
  downloader, the agent's own model API — and where listing every such host in
  `NO_PROXY` instead is a list that is always one host short.

  What passes through is a blind tunnel: no interception, no credential, no
  policy beyond "the bearer presented a valid token".  The tunnel is audited. -/
  passthrough : List String := []
  /-- The programs allowed to ask for tokens. -/
  issuers : List Issuer := []
  deriving Repr, Inhabited

/-- May a host no manifest claims be reached through the proxy? -/
def Config.passes (c : Config) (host : String) : Bool :=
  c.passthrough.any fun p => Facts.hostMatches (Str.toLowerAscii p) (Str.toLowerAscii host)

/-- An issuer by name. -/
def Config.issuer? (c : Config) (name : String) : Option Issuer :=
  c.issuers.find? (·.name == name)

/-- Read an issuer from a table. -/
private def issuerOf (j : Json) : Except String Issuer := do
  let some name := j.str? "name" | throw "an issuer needs a `name`"
  let strings (k : String) := (j.arr? k).filterMap Json.asString?
  let maxTtl ← match j.str? "max_ttl" with
    | none => pure 86400
    | some d => match Policy.parseDuration? d with
      | some n => pure n
      | none => throw s!"`{d}` is not a duration"
  let facts := strings "facts"
  for p in facts do
    if p == "*" || p.isEmpty then
      throw s!"the issuer `{name}` may not be allowed every fact; name a prefix such as `task_*`"
  let tokenTtl ← match j.str? "token_ttl" with
    | none => pure (365 * 86400)
    | some d => match Policy.parseDuration? d with
      | some n => pure n
      | none => throw s!"`{d}` is not a duration"
  pure { name, grants := strings "grants", facts, maxTtl, tokenFile := j.str? "token_file", tokenTtl }

/-- Read a configuration from TOML. -/
def Config.ofToml (source : String) : Except String Config := do
  let j ← Toml.parse source
  let listen := (j.str? "listen").getD "127.0.0.1:8080"
  let (host, port) := match Str.splitOnce? listen ":" with
    | some (h, p) => (h, (p.toNat?.getD 8080))
    | none => (listen, 8080)
  let mode ← match (j.str? "mode").getD "both" with
    | "connect" => pure Mode.connect
    | "rewrite" => pure Mode.rewrite
    | "both" => pure Mode.both
    | other => throw s!"unknown mode `{other}`"
  let limits := (j.field? "limits").getD (.obj [])
  let issuers ← (j.arr? "issuer").mapM issuerOf
  pure {
    listenHost := host, listenPort := UInt16.ofNat port, mode
    upstreamCaFile := (j.str? "upstream_ca_file").getD ""
    maxHeadSize := ((limits.int? "max_head_size").getD 65536).toNat
    maxDecodePrefix := ((limits.int? "max_decode_prefix").getD 65536).toNat
    maxBodyFacts := ((limits.int? "max_body_facts").getD 256).toNat
    maxRequestsPerConnection := ((limits.int? "max_requests_per_connection").getD 100).toNat
    upstreamIdleSeconds := ((limits.int? "upstream_idle_seconds").getD 30).toNat
    audit := (j.bool? "audit").getD true
    passthrough := (j.arr? "passthrough").filterMap Json.asString?
    issuers }

/-- Load the configuration, or the defaults if there is no file. -/
def loadConfig : IO Config := do
  match ← Store.read? ((← Dirs.config) / "config.toml") with
  | none => return {}
  | some text =>
    match Config.ofToml text with
    | .ok c => return c
    | .error e => throw (IO.userError s!"the configuration is invalid: {e}")

end Kleis
