import Kleis.Service.Registry
import Kleis.Credential.Provider
import Kleis.Token.Revocation
import Kleis.Ca.Mint
import Kleis.Config
import Kleis.Audit

/-!
# The daemon's shared state

One value, passed to every connection.  What is mutable in it is mutable
because it is reloaded (`registry`, `revocations`) or cached (`ca`,
`credentials`); nothing here is per-request.
-/

namespace Kleis
namespace Proxy

open LeanBiscuit

/-- Idle connections to origins, kept for the next request to the same one.

Keyed by scheme, host and port.  A connection is handed out to one request at a
time — taken out of the pool while in use and put back when its response has
been relayed in full — so no two requests ever share one.  Entries older than
the configured idle time are closed rather than handed out, and the pool is
bounded so that a burst of parallel requests does not leave a socket per
request lying around afterwards. -/
structure Pool where
  /-- Key, connection, and when it went idle. -/
  idle : IO.Ref (Array (String × Net.Stream × Nat))
  /-- How long an idle connection is trusted, in seconds. -/
  maxIdle : Nat
  /-- How many idle connections are kept at most. -/
  capacity : Nat := 64

/-- An empty pool. -/
def Pool.create (maxIdle : Nat) : IO Pool := do
  return { idle := ← IO.mkRef #[], maxIdle }

/-- Take an idle connection to this origin, if a fresh enough one is there. -/
def Pool.take? (p : Pool) (key : String) : IO (Option Net.Stream) := do
  let now ← Store.now
  let (found, stale) ← p.idle.modifyGet fun entries =>
    let stale := entries.filter fun (_, _, t) => now > t + p.maxIdle
    let live := entries.filter fun (_, _, t) => now ≤ t + p.maxIdle
    match live.findIdx? (fun (k, _, _) => k == key) with
    | some i =>
      match live[i]? with
      | some (_, s, _) => ((some s, stale), live.eraseIdxIfInBounds i)
      | none => ((none, stale), live)
    | none => ((none, stale), live)
  for (_, s, _) in stale do
    try s.close catch _ => pure ()
  return found

/-- Put a connection back after its response was relayed in full. -/
def Pool.put (p : Pool) (key : String) (s : Net.Stream) : IO Unit := do
  let now ← Store.now
  let evicted ← p.idle.modifyGet fun entries =>
    let entries := entries.push (key, s, now)
    if entries.size > p.capacity then
      (entries[0]?.map (·.2.1), entries.eraseIdxIfInBounds 0)
    else (none, entries)
  if let some old := evicted then
    try old.close catch _ => pure ()

/-- Facts remembered for tokens: what a route's `on_success` asked to be kept
when a request succeeded, such as the repository a token created, asserted on
that token's later requests so its grant can let it push to what it made.

Keyed by the token's *authority* revocation identifier, which every attenuation
of the token shares: a job that narrowed its token before handing it to a
sub-step still finds the repository it created.  Kept in one append-only file
so a restart does not forget, and in memory behind a mutex. -/
structure Memory where
  private mk ::
  private entries : Std.Mutex (Array (String × Builder.Fact))

/-- The key a token's memories are filed under. -/
def Memory.keyOf (token : LeanBiscuit.Token.Biscuit) : String :=
  ((LeanBiscuit.Token.Biscuit.revocationIdentifiers token).head?.map Bytes.toHex).getD ""

/-- Load what was remembered before. -/
def Memory.load : IO Memory := do
  let mut entries : Array (String × Builder.Fact) := #[]
  if let some text ← Store.read? (← Dirs.remembered) then
    for line in text.splitOn "\n" do
      if let .ok j := Json.parse line then
        if let (some key, some fj) := (j.str? "token", j.field? "fact") then
          if let .ok f := Token.factOfJson fj then
            entries := entries.push (key, f)
  return ⟨← Std.Mutex.new entries⟩

/-- The facts remembered for a token. -/
def Memory.factsFor (m : Memory) (token : LeanBiscuit.Token.Biscuit) : IO (List Builder.Fact) :=
  let key := Memory.keyOf token
  m.entries.atomically do
    return ((← get).filter (·.1 == key)).toList.map (·.2)

/-- Remember facts for a token, once each. -/
def Memory.add (m : Memory) (token : LeanBiscuit.Token.Biscuit) (facts : List Builder.Fact) :
    IO Unit := do
  let key := Memory.keyOf token
  if key.isEmpty then return
  m.entries.atomically do
    for f in facts do
      let some fj := Token.factToJson? f | continue
      let rendered := Json.render fj
      let known := (← get).any fun (k, g) =>
        k == key && ((Token.factToJson? g).map Json.render) == some rendered
      if !known then
        Store.appendLine (← Dirs.remembered)
          (Json.render (.obj [("token", .str key), ("fact", fj)]))
        modify (·.push (key, f))

/-- Everything a connection handler needs. -/
structure Context where
  /-- The configuration read at startup. -/
  config : Config
  /-- Manifests and grants, replaced wholesale on reload. -/
  registry : IO.Ref Service.Registry
  /-- The biscuit root key, for verifying the tokens bearers present. -/
  rootPublic : PublicKey
  /-- Certificates for interception. -/
  ca : Ca.Cache
  /-- The context used to verify origins. -/
  clientCtx : Net.Tls.Context
  /-- Live credentials, cached until they expire. -/
  credentials : Credential.Cache
  /-- The revocation list, replaced on reload. -/
  revocations : IO.Ref Token.Revocations
  /-- A counter behind the request identifiers. -/
  counter : IO.Ref Nat
  /-- The audit log, whose chain every connection extends. -/
  audit : AuditLog
  /-- Idle connections to origins. -/
  pool : Pool
  /-- Facts remembered for tokens. -/
  memory : Memory

/-- Build the shared state. -/
def Context.create (config : Config) : IO Context := do
  let registry ← Service.Registry.load
  let root ← Token.rootPublicKey
  let caRoot ← Ca.loadOrCreateRoot
  -- The store is resolved and then checked, rather than trusted to have
  -- loaded: a context that trusts nothing fails on the first request with a
  -- message about certificates rather than about configuration.
  let trustStore ← Net.resolveTrustStore config.upstreamCaFile
  let clientCtx ← Net.Tls.mkClientContext trustStore
  let trusted ← Net.Tls.contextSize clientCtx
  if trusted == 0 then
    throw (IO.userError <|
      (if trustStore.isEmpty then
         "no system trust store was found, and the linked OpenSSL's own default is empty"
       else s!"the trust store `{trustStore}` contains no certificates")
      ++ "\n  origins could not be verified, so nothing would be proxied."
      ++ "\n  set `upstream_ca_file` in config.toml to your system CA bundle,"
      ++ "\n  such as /etc/ssl/certs/ca-certificates.crt")
  return {
    config
    registry := ← IO.mkRef registry
    rootPublic := root
    ca := ← Ca.Cache.create caRoot
    clientCtx
    credentials := ← Credential.Cache.create
    revocations := ← IO.mkRef (← Token.loadRevocations)
    counter := ← IO.mkRef 0
    audit := ← AuditLog.create
    pool := ← Pool.create config.upstreamIdleSeconds
    memory := ← Memory.load }

/-- Re-read manifests, grants and revocations, and forget cached credentials. -/
def Context.reload (ctx : Context) : IO Unit := do
  -- Loaded before anything is replaced, so a registry that fails to load
  -- leaves the old one in place rather than half of a new one.
  let registry ← Service.Registry.load
  let revocations ← Token.loadRevocations
  ctx.registry.set registry
  ctx.revocations.set revocations
  ctx.credentials.clear

/-- What the files a reload reads look like now: each one's path and modification
time.  Two equal snapshots mean nothing a reload would read has changed. -/
def reloadSnapshot (files : Array System.FilePath) : IO (List (String × String)) :=
  files.toList.filterMapM fun f => do
    try
      let m ← f.metadata
      return some (f.toString, s!"{m.modified.sec}.{m.modified.nsec}:{m.byteSize}")
    catch _ => return none

/-- Reload whenever the files change, until the process ends.

`kleis token revoke` and `kleis credential add` write files and nothing else; a
daemon that read them only at startup would go on honouring a revoked token
until somebody restarted it, which is the opposite of what revoking is for.  So
the daemon looks every few seconds.  A reload that fails — a grant somebody is
halfway through editing — is reported and the configuration already loaded is
kept: a daemon that stopped serving because of a typo would be worse than one
that serves the last configuration that loaded. -/
partial def Context.watch (ctx : Context) (log : String → IO Unit)
    (intervalMs : UInt32 := 3000) : IO Unit := do
  -- Two snapshots, because a revocation is far more frequent than an edit and
  -- should not cost the credential cache: an orchestrator revoking a token at
  -- the end of every job would otherwise have every installation token
  -- re-minted after every job.
  let configFiles : IO (Array System.FilePath) := do
    return (← Store.listFiles (← Dirs.services) "toml")
      ++ (← Store.listFiles (← Dirs.grants) "toml")
      ++ (← Store.listFiles (← Dirs.credentials) "json")
      ++ (← Store.listFiles ((← Dirs.config) / "credentials") "toml")
  let snapshot : IO (List (String × String) × List (String × String)) := do
    return (← reloadSnapshot (← configFiles), ← reloadSnapshot #[← Dirs.revocations])
  let rec loop (last : List (String × String) × List (String × String)) : IO Unit := do
    IO.sleep intervalMs
    let now ← try snapshot catch _ => pure last
    if now.1 != last.1 then
      try
        ctx.reload
        log "kleis: configuration changed; reloaded"
      catch e =>
        log s!"kleis: configuration changed but did not load, keeping the previous one: {e}"
        -- Revocations do not depend on the rest loading.
        try ctx.revocations.set (← Token.loadRevocations) catch _ => pure ()
    else if now.2 != last.2 then
      try ctx.revocations.set (← Token.loadRevocations)
      catch e => log s!"kleis: the revocation list did not load: {e}"
    loop now
  loop (← snapshot)

/-- A fresh request identifier: a counter and some entropy, so that two
daemons' logs can be concatenated without collisions. -/
def Context.nextRequestId (ctx : Context) : IO String := do
  let n ← ctx.counter.modifyGet fun n => (n, n + 1)
  return s!"{← Store.randomId 4}-{n}"

end Proxy
end Kleis
