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
    counter := ← IO.mkRef 0 }

/-- Re-read manifests, grants and revocations, and forget cached credentials. -/
def Context.reload (ctx : Context) : IO Unit := do
  ctx.registry.set (← Service.Registry.load)
  ctx.revocations.set (← Token.loadRevocations)
  ctx.credentials.clear

/-- A fresh request identifier: a counter and some entropy, so that two
daemons' logs can be concatenated without collisions. -/
def Context.nextRequestId (ctx : Context) : IO String := do
  let n ← ctx.counter.modifyGet fun n => (n, n + 1)
  return s!"{← Store.randomId 4}-{n}"

end Proxy
end Kleis
