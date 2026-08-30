import Kleis.Service.Manifest
import Kleis.Policy.Grant
import Kleis.Store

/-!
# Loading manifests and grants

Manifests come from `$KLEIS_HOME/config/services/*.toml`, grants from
`grants/*.toml`.  Both are read at startup and on reload, and a file that does
not parse is a startup failure rather than a warning: a manifest that silently
failed to load would turn a policy into a permissive one, because the routes it
was going to emit facts for would simply be missing.
-/

namespace Kleis
namespace Service

/-- Everything loaded from configuration. -/
structure Registry where
  /-- Manifests by name. -/
  manifests : Array Manifest
  /-- Grants by name. -/
  grants : Array Policy.Grant
  deriving Inhabited

/-- Load every manifest and grant. -/
def Registry.load : IO Registry := do
  let mut manifests : Array Manifest := #[]
  for f in ← Store.listFiles (← Dirs.services) "toml" do
    let text ← IO.FS.readFile f
    match Manifest.ofToml text with
    | .ok m => manifests := manifests.push m
    | .error e => throw (IO.userError s!"{f}: {e}")
  let mut grants : Array Policy.Grant := #[]
  for f in ← Store.listFiles (← Dirs.grants) "toml" do
    let text ← IO.FS.readFile f
    match Policy.Grant.ofToml text with
    | .ok g => grants := grants.push g
    | .error e => throw (IO.userError s!"{f}: {e}")
  -- A grant naming a service nobody has a manifest for can never be satisfied,
  -- and saying so at startup is better than at three in the morning.
  for g in grants do
    if !(manifests.any fun m => m.name == g.service) then
      throw (IO.userError
        s!"the grant `{g.name}` names the service `{g.service}`, which has no manifest")
  return { manifests, grants }

/-- The manifest claiming a host. -/
def Registry.forHost? (r : Registry) (host : String) : Option Manifest :=
  Array.find? (fun m => m.claims host) r.manifests

/-- A manifest by name. -/
def Registry.manifest? (r : Registry) (name : String) : Option Manifest :=
  Array.find? (fun m => m.name == name) r.manifests

/-- A grant by name. -/
def Registry.grant? (r : Registry) (name : String) : Option Policy.Grant :=
  Array.find? (fun g => g.name == name) r.grants

end Service
end Kleis
