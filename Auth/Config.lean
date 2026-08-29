import Auth.Util.Toml
import Auth.Dirs
import Auth.Store

/-!
# Configuration

`$AUTH_HOME/config/config.toml`, or the defaults below, which are chosen so
that a daemon started with no configuration at all does something safe and
useful: listen on the loopback, accept both interception modes, and refuse
anything it has no manifest for.
-/

namespace Auth

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
  /-- Whether to write an audit record for every decision. -/
  audit : Bool := true
  deriving Repr, Inhabited

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
  pure {
    listenHost := host, listenPort := UInt16.ofNat port, mode
    upstreamCaFile := (j.str? "upstream_ca_file").getD ""
    maxHeadSize := ((limits.int? "max_head_size").getD 65536).toNat
    maxDecodePrefix := ((limits.int? "max_decode_prefix").getD 65536).toNat
    maxBodyFacts := ((limits.int? "max_body_facts").getD 256).toNat
    maxRequestsPerConnection := ((limits.int? "max_requests_per_connection").getD 100).toNat
    audit := (j.bool? "audit").getD true }

/-- Load the configuration, or the defaults if there is no file. -/
def loadConfig : IO Config := do
  match ← Store.read? ((← Dirs.config) / "config.toml") with
  | none => return {}
  | some text =>
    match Config.ofToml text with
    | .ok c => return c
    | .error e => throw (IO.userError s!"the configuration is invalid: {e}")

end Auth
