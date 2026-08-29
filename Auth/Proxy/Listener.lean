import Auth.Proxy.Session

/-!
# The accept loop

Bind, accept, and hand each connection to a dedicated task.

A connection that fails takes nothing else with it: the handler catches
everything, because a malformed request from one client must not stop the
daemon serving the others.  What it does not do is swallow the reason — every
failure is logged with the address it came from.
-/

namespace Auth
namespace Proxy

open LeanBiscuit

/-- Write a line to standard error, flushed, so that a daemon whose output is
piped somewhere still says what it is doing as it happens. -/
def log (message : String) : IO Unit := do
  let h ← IO.getStderr
  h.putStrLn message
  h.flush

/-- Accept connections until the process ends.

`partial` because it genuinely does not terminate: a daemon's accept loop has
no measure that decreases.  This is the boundary the design draws — everything
from `Auth.Model` through `Auth.Policy` is total, and the loops that are not
are the ones whose whole purpose is to run forever. -/
partial def acceptLoop (ctx : Context) (server : Std.Internal.UV.TCP.Socket) : IO Unit := do
  let client ← Net.Tcp.accept server
  let peer := client.describe
  let _ ← IO.asTask (prio := .dedicated) do
    try
      handleConnection ctx client peer
    catch e =>
      log s!"auth: {peer}: {e}"
    try client.close catch _ => pure ()
  acceptLoop ctx server

/-- Serve until the process ends. -/
def serve (ctx : Context) : IO Unit := do
  let (server, port) ← Net.Tcp.listen ctx.config.listenHost ctx.config.listenPort
  log s!"auth: listening on {ctx.config.listenHost}:{port}"
  let registry ← ctx.registry.get
  log s!"auth: {registry.manifests.size} service(s), {registry.grants.size} grant(s)"
  for m in registry.manifests do
    log s!"auth:   {m.name} → {String.intercalate ", " m.hosts}"
  acceptLoop ctx server

end Proxy
end Auth
