import Auth

/-!
# The daemon

The process that holds credentials.  It reads the configuration, loads the
manifests and grants, opens the listening socket, and serves until it is
stopped.

Separate from `auth` so that neither ships the other's job: the client can be
run by anybody, and the only program that ever decrypts a credential is this
one.
-/

open Auth

/-- Report a startup failure and stop, rather than serving in a state where
some manifests loaded and others did not. -/
private def fail (message : String) : IO UInt32 := do
  let h ← IO.getStderr
  h.putStrLn s!"authd: {message}"
  h.flush
  return 1

def main (argv : List String) : IO UInt32 := do
  if argv.contains "--help" then
    IO.println "authd — the auth daemon\n\nusage: authd [--check]\n\n\
      --check  load everything and report, without listening"
    return 0
  try
    let config ← loadConfig
    let ctx ← Proxy.Context.create config
    if argv.contains "--check" then
      let registry ← ctx.registry.get
      Proxy.log s!"authd: {registry.manifests.size} service(s), {registry.grants.size} grant(s)"
      for m in registry.manifests do
        Proxy.log s!"authd:   {m.name} → {String.intercalate ", " m.hosts}"
      for g in registry.grants do
        Proxy.log s!"authd:   grant {g.name} → {g.service} via {g.credential}"
      Proxy.log "authd: configuration is loadable"
      return 0
    Proxy.serve ctx
    return 0
  catch e => fail (toString e)
