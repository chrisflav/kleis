import Kleis.Util.Json

/-!
# Where things live

Config in `$XDG_CONFIG_HOME/kleis`, state in `$XDG_DATA_HOME/kleis`, both
overridable with `$KLEIS_HOME` for a self-contained installation and for tests,
which must never touch the invoking user's real credentials.
-/

namespace Kleis
namespace Dirs

/-- The environment variable that overrides everything below. -/
def homeVar : String := "KLEIS_HOME"

/-- A programmatic override, which takes precedence over the environment.

It exists for the test suite, which must never read or write the credentials of
whoever is running it, and which cannot set an environment variable for itself
— Lean's `IO` has `getEnv` and no `setEnv`. -/
initialize override : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- Point every directory below at `path`. -/
def useHome (path : System.FilePath) : IO Unit := override.set (some path)

/-- Resolve a directory: `$KLEIS_HOME/<sub>` when set, else `$<xdg>/kleis`, else
`$HOME/<fallback>/kleis`. -/
private def resolve (sub xdg fallback : String) : IO System.FilePath := do
  if let some h ← override.get then
    return h / sub
  if let some h ← IO.getEnv homeVar then
    return System.FilePath.mk h / sub
  if let some d ← IO.getEnv xdg then
    return System.FilePath.mk d / "kleis"
  let home := (← IO.getEnv "HOME").getD "."
  return System.FilePath.mk home / fallback / "kleis"

/-- Where configuration, manifests and grants are read from. -/
def config : IO System.FilePath := resolve "config" "XDG_CONFIG_HOME" ".config"

/-- Where credentials, keys, tokens and the audit log are kept. -/
def data : IO System.FilePath := resolve "data" "XDG_DATA_HOME" ".local/share"

/-- Service manifests. -/
def services : IO System.FilePath := do return (← config) / "services"

/-- Grants. -/
def grants : IO System.FilePath := do return (← config) / "grants"

/-- Encrypted credentials. -/
def credentials : IO System.FilePath := do return (← data) / "credentials"

/-- The certificate authority for intercepting mode. -/
def ca : IO System.FilePath := do return (← data) / "ca"

/-- The audit log. -/
def auditLog : IO System.FilePath := do return (← data) / "audit.log"

/-- Issued token records, by revocation identifier. -/
def issued : IO System.FilePath := do return (← data) / "issued"

/-- The revocation list. -/
def revocations : IO System.FilePath := do return (← data) / "revoked"

end Dirs
end Kleis
