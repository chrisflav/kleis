import Kleis.Service.Manifest
import Kleis.Service.Extension
import Kleis.Policy.Grant
import Kleis.Spec
import Kleis.Config
import Kleis.Store

/-!
# Loading manifests and grants

Manifests come from `$KLEIS_HOME/config/services/*.toml` and from the enabled
extensions (`Kleis.Service.Extension`), grants from `grants/*.toml` and from the specs
in `specs/*.kleis`, each compiled into one grant per account (`Kleis.Spec`).  Both are read at startup and on reload, and a file that does
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
  /-- Grants by name: the files', then every spec's compiled ones. -/
  grants : Array Policy.Grant
  /-- The enabled extensions. -/
  extensions : Array Extension := #[]
  /-- Specs by name, compiled. -/
  specs : Array Kleis.Spec.Spec := #[]
  deriving Inhabited

/-- Load every manifest, extension, grant and spec. -/
def Registry.load (config? : Option Config := none) : IO Registry := do
  let config ← match config? with
    | some c => pure c
    | none => loadConfig
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
  -- Extensions, each bringing its manifest. A service with dynamic hosts claims every
  -- host an account of it is bound to, plus those the configuration adds.
  let credentials ← Credential.list
  let mut extensions : Array Extension := #[]
  let mut extensionManifests : List (Extension × Manifest) := []
  for name in config.extensions.eraseDups do
    let e ← Extension.load name
    if manifests.any (·.name == e.service) then
      throw (IO.userError s!"the extension `{name}` and a manifest under services/ both claim `{e.service}`")
    let hosts := ((credentials.toList.filter (·.service == e.service)).flatMap (·.hosts)
      ++ ((config.extensionHosts.find? (·.1 == name)).map (·.2)).getD []).eraseDups
    let m ← match e.manifest hosts with
      | .ok m => pure m
      | .error err => throw (IO.userError s!"{e.dir / "manifest.toml"}: {err}")
    if let .error err := e.check m then throw (IO.userError s!"{e.dir}: {err}")
    manifests := manifests.push m
    extensions := extensions.push e
    extensionManifests := extensionManifests ++ [(e, m)]
  -- Two manifests claiming one host would make which one decides a request depend on
  -- load order.
  for m in manifests do
    for h in m.hosts do
      for other in manifests do
        if other.name != m.name && other.hosts.contains h then
          throw (IO.userError s!"`{h}` is claimed by both `{m.name}` and `{other.name}`")
  -- Specs, compiled against the extensions, the credentials and the grant files.
  let env : Kleis.Spec.Env := { extensions := extensionManifests, credentials, grants }
  let mut specs : Array Kleis.Spec.Spec := #[]
  for f in ← Store.listFiles (← Dirs.specs) "kleis" do
    let text ← IO.FS.readFile f
    match Kleis.Spec.load text env with
    | .ok s =>
      if specs.any (·.name == s.name) then throw (IO.userError s!"{f}: a second spec `{s.name}`")
      for a in s.accounts do
        if grants.any (·.name == a.grant.name) then
          throw (IO.userError s!"{f}: the compiled grant `{a.grant.name}` has the name of a grant file")
      specs := specs.push s
    | .error e => throw (IO.userError s!"{f}: {e}")
  grants := grants ++ (specs.toList.flatMap fun s => s.accounts.map (·.grant)).toArray
  -- A grant naming a service nobody has a manifest for can never be satisfied,
  -- and saying so at startup is better than at three in the morning.
  for g in grants do
    if !(manifests.any fun m => m.name == g.service) then
      throw (IO.userError
        s!"the grant `{g.name}` names the service `{g.service}`, which has no manifest")
  return { manifests, grants, extensions, specs }

/-- The manifest claiming a host. -/
def Registry.forHost? (r : Registry) (host : String) : Option Manifest :=
  Array.find? (fun m => m.claims host) r.manifests

/-- A manifest by name. -/
def Registry.manifest? (r : Registry) (name : String) : Option Manifest :=
  Array.find? (fun m => m.name == name) r.manifests

/-- A grant by name. -/
def Registry.grant? (r : Registry) (name : String) : Option Policy.Grant :=
  Array.find? (fun g => g.name == name) r.grants

/-- A spec by name. -/
def Registry.spec? (r : Registry) (name : String) : Option Kleis.Spec.Spec :=
  Array.find? (fun s => s.name == name) r.specs

/-- An extension by service. -/
def Registry.extension? (r : Registry) (service : String) : Option Extension :=
  Array.find? (fun e => e.service == service) r.extensions

/-- The grants a spec stands for, in order: its accounts' compiled grants, then the grants
it includes — each of those carrying `grant(<its name>)` as a fact of its own, so that a
grant file written to be named by a token (`allow if grant("orchestra-github")`) decides the
same way when a spec includes it. That fact is the grant's, asserted by the authorizer, and
says what the spec already said; a token cannot put it there. -/
def Registry.specGrants (r : Registry) (s : Kleis.Spec.Spec) : List Policy.Grant :=
  s.accounts.map (·.grant) ++ s.includes.filterMap fun name =>
    (r.grant? name).map fun g =>
      { g with facts := g.facts ++ [⟨⟨"grant", [.str g.name]⟩⟩] }

/-- The longest a token naming a spec may live: the spec's bound, and every included
grant's. -/
def Registry.specLifetime (r : Registry) (s : Kleis.Spec.Spec) : Nat :=
  s.includes.foldl (fun acc name => match r.grant? name with
    | some g => min acc g.maxLifetime
    | none => acc) s.maxTtl

end Service
end Kleis
