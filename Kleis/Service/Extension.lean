import Kleis.Service.Manifest
import Kleis.Util.Toml
import Kleis.Store

/-!
# Extensions

An extension is everything kleis knows about one kind of service, in one directory:

```
extensions/zulip/
  manifest.toml     what its requests mean (`Kleis.Service.Manifest`)
  extension.toml    the words a spec may use for it, the prose a card is written in,
                    and what a sandbox needs to talk to it
  README.md
```

The manifest is the part that decides; the rest is vocabulary and presentation. A spec
(`Kleis.Spec`) is written in an extension's vocabulary — operation names, groups of them,
fields a condition may test — and compiled to datalog over the facts the manifest emits. A
card (`Kleis.Card`) is the same spec rendered back into the extension's prose. A sandbox's
setup (`/.kleis/v1/setup`) is what the extension says a client needs: a placeholder token where
a client insists on one, a config file pointing at the right server.

## Hosts

A service with one set of servers (GitHub) lists them in its manifest. A service whose servers
vary from account to account (Zulip, CalDAV) is `hosts = "dynamic"`: its manifest lists none,
and claims every host an account of that service is bound to, plus any the operator adds in
`config.toml`. An account of such a service must name its hosts, so that one server's key is
never sent to another (`Credential.Record.hosts`).

## Where extensions are found

Enabled by name in `config.toml` (`extensions = ["github", "zulip"]`) and looked up in
`$KLEIS_HOME/config/extensions/<name>`, then `$KLEIS_EXTENSIONS_DIR/<name>`, then
`/usr/share/kleis/extensions/<name>`, the first that exists. The image ships the repository's
`extensions/` at the last of these; a deployment can override one by putting its own first.
-/

namespace Kleis
namespace Service

/-- A field a spec's condition may test: a fact the manifest emits about a request. -/
structure Field where
  /-- The name a spec uses. -/
  name : String
  /-- The predicate carrying it, with the value as its only term. -/
  fact : String
  /-- `string`, `int` or `bool`. -/
  type : String
  /-- Whether a request carries at most one value (`false`) or one fact per value (`true`). -/
  multi : Bool
  /-- How a card says it: "to the stream", "every recipient's address". -/
  phrase : String
  deriving Repr, Inhabited

/-- A named set of operations a spec may allow at once. -/
structure Group where
  /-- The name a spec uses. -/
  name : String
  /-- The manifest operations it stands for. -/
  operations : List String
  /-- How a card says it. -/
  phrase : String
  deriving Repr, Inhabited

/-- A file a sandbox needs, written relative to its home. -/
structure SetupFile where
  /-- Relative to the home directory; `{host}` and `{account}` are filled per account. -/
  path : String
  /-- An octal mode, such as `0600`. -/
  mode : Option String
  /-- The contents; the same placeholders are filled. -/
  content : String
  /-- Written once per account (`{host}` in the path tells them apart), or once in all. -/
  perAccount : Bool
  deriving Repr, Inhabited

/-- An extension, loaded. -/
structure Extension where
  /-- The service, which is its manifest's name. -/
  service : String
  /-- How a card names the service. -/
  display : String
  /-- How a card tells the agent which client to use. -/
  client : String
  /-- Whether its hosts come from its accounts. -/
  dynamicHosts : Bool
  /-- Groups of operations. -/
  groups : List Group
  /-- How a card says each manifest operation. -/
  operations : List (String × String)
  /-- Fields a spec may test. -/
  fields : List Field
  /-- How a card renders an authority fact: predicate, and a template with `{0}`, `{1}` for
  its terms. -/
  factPhrases : List (String × String)
  /-- Environment a sandbox needs; no secrets. -/
  env : List (String × String)
  /-- Files a sandbox needs; no secrets. -/
  files : List SetupFile
  /-- The manifest's source, parsed once the hosts are known. -/
  manifestSource : String
  /-- Where it was loaded from. -/
  dir : System.FilePath
  deriving Inhabited

/-- The operation names a manifest emits as `operation("…")` constants. -/
def Manifest.operations (m : Manifest) : List String :=
  (m.routes.flatMap fun r => r.emit.filterMap fun f =>
    if f.predicate.name != "operation" then none
    else match f.predicate.terms with
      | [.str s] => some s
      | _ => none).eraseDups

/-- The operations a name in a spec stands for: a group's, or one the manifest emits. -/
def Extension.expand (e : Extension) (manifestOps : List String) (name : String) :
    Option (List String) :=
  match e.groups.find? (·.name == name) with
  | some g => some g.operations
  | none => if manifestOps.contains name then some [name] else none

/-- How a card says an operation or a group. -/
def Extension.phraseOf (e : Extension) (name : String) : String :=
  match e.groups.find? (·.name == name) with
  | some g => g.phrase
  | none => ((e.operations.find? (·.1 == name)).map (·.2)).getD name

/-- A field by name. -/
def Extension.field? (e : Extension) (name : String) : Option Field :=
  e.fields.find? (·.name == name)

/-- Is a path one a sandbox may be given: relative, and never climbing out of where it is
written? Absolute paths, `..` segments, empty segments and backslashes are refused. -/
def safeRelativePath (p : String) : Bool :=
  !p.isEmpty && !p.startsWith "/" && !p.startsWith "~" && !p.contains '\\'
    && (p.splitOn "/").all fun s => !s.isEmpty && s != ".." && s != "."

/-- The environment variables a sandbox's own launcher owns, which no extension may set. -/
def reservedEnv : List String :=
  ["HTTPS_PROXY", "HTTP_PROXY", "https_proxy", "http_proxy", "NO_PROXY", "no_proxy",
   "ALL_PROXY", "all_proxy", "SSL_CERT_FILE", "SSL_CERT_DIR", "GIT_SSL_CAINFO",
   "CURL_CA_BUNDLE", "REQUESTS_CA_BUNDLE", "NODE_EXTRA_CA_CERTS", "HOME", "PATH"]

private def strings (j : Json) (k : String) : List String := (j.arr? k).filterMap Json.asString?

private def tableEntries (j : Json) (k : String) : List (String × Json) :=
  match j.field? k with
  | some (.obj fields) => fields
  | _ => []

/-- Read an extension's `extension.toml`, beside its manifest's source. -/
def Extension.ofToml (source manifestSource : String) (dir : System.FilePath) :
    Except String Extension := do
  let j ← Toml.parse source
  let some service := j.str? "service" | throw "an extension needs a `service`"
  let dynamicHosts ← match (j.str? "hosts").getD "fixed" with
    | "fixed" => pure false
    | "dynamic" => pure true
    | other => throw s!"`hosts` is \"fixed\" or \"dynamic\", not `{other}`"
  let groups ← (tableEntries j "groups").mapM fun (name, g) => do
    let ops := strings g "operations"
    if ops.isEmpty then throw s!"the group `{name}` lists no `operations`"
    pure ({ name, operations := ops, phrase := (g.str? "phrase").getD name } : Group)
  let operations := (tableEntries j "operations").filterMap fun (name, v) =>
    v.asString?.map (name, ·)
  let fields ← (tableEntries j "fields").mapM fun (name, f) => do
    let type := (f.str? "type").getD "string"
    if !["string", "int", "bool"].contains type then
      throw s!"the field `{name}` has type `{type}`; it is string, int or bool"
    let multi ← match (f.str? "values").getD "single" with
      | "single" => pure false
      | "multi" => pure true
      | other => throw s!"the field `{name}` has values `{other}`; it is single or multi"
    pure ({ name, fact := (f.str? "fact").getD name, type, multi
            phrase := (f.str? "phrase").getD name } : Field)
  let factPhrases := (tableEntries j "facts").filterMap fun (name, v) => v.asString?.map (name, ·)
  let setup := (j.field? "setup").getD (.obj [])
  let env := (tableEntries setup "env").filterMap fun (k, v) => v.asString?.map (k, ·)
  for (k, _) in env do
    if reservedEnv.contains k then
      throw s!"the setup may not set `{k}`: that is the sandbox launcher's"
  let files ← (setup.arr? "files").mapM fun f => do
    let some path := f.str? "path" | throw "a setup file needs a `path`"
    let content ← match f.str? "content", f.str? "content_file" with
      | some c, none => pure c
      | none, some _ => pure ""   -- read by `load`, which can do IO
      | _, _ => throw s!"the setup file `{path}` needs `content` or `content_file`, not both"
    pure ({ path, mode := f.str? "mode", content
            perAccount := (f.bool? "per_account").getD false } : SetupFile)
  for f in files do
    -- `{host}` is a host name, so filling it cannot make a safe path unsafe.
    if !safeRelativePath f.path then
      throw s!"the setup file `{f.path}` is not a path relative to the home directory"
  pure { service, display := (j.str? "display").getD service
         client := (j.str? "client").getD ""
         dynamicHosts, groups, operations, fields, factPhrases, env, files
         manifestSource, dir }

/-- The directories an extension is looked for in, in order. -/
def extensionSearchPath : IO (List System.FilePath) := do
  let fromEnv := (← IO.getEnv "KLEIS_EXTENSIONS_DIR").toList.map System.FilePath.mk
  return [(← Dirs.config) / "extensions"] ++ fromEnv
    ++ [System.FilePath.mk "/usr/share/kleis/extensions"]

/-- Load one extension by name. -/
def Extension.load (name : String) : IO Extension := do
  if name.isEmpty || name.contains '/' || name.startsWith "." then
    throw (IO.userError s!"`{name}` is not an extension name")
  let mut found : Option System.FilePath := none
  for base in ← extensionSearchPath do
    if found.isNone && (← (base / name / "extension.toml").pathExists) then
      found := some (base / name)
  let some dir := found
    | throw (IO.userError s!"the extension `{name}` is enabled but was found in none of {(← extensionSearchPath).map toString}")
  let source ← IO.FS.readFile (dir / "extension.toml")
  let manifestSource ← IO.FS.readFile (dir / "manifest.toml")
  let e ← match Extension.ofToml source manifestSource dir with
    | .ok e => pure e
    | .error err => throw (IO.userError s!"{dir / "extension.toml"}: {err}")
  if e.service != name then
    throw (IO.userError s!"{dir / "extension.toml"}: the extension `{name}` says it is `{e.service}`")
  -- Files given by `content_file` are read now, relative to the extension.
  let j ← match Toml.parse source with
    | .ok j => pure j
    | .error err => throw (IO.userError err)
  let setup := (j.field? "setup").getD (.obj [])
  let mut files : List SetupFile := []
  for (f, fj) in e.files.zip (setup.arr? "files") do
    match fj.str? "content_file" with
    | some rel =>
      if !safeRelativePath rel then
        throw (IO.userError s!"{dir}: `content_file = {rel}` must be a path inside the extension")
      files := files ++ [{ f with content := ← IO.FS.readFile (dir / rel) }]
    | none => files := files ++ [f]
  return { e with files }

/-- The extension's manifest, claiming these hosts if its hosts are dynamic. -/
def Extension.manifest (e : Extension) (dynamicHosts : List String) : Except String Manifest :=
  if e.dynamicHosts then Manifest.ofToml e.manifestSource (some dynamicHosts)
  else Manifest.ofToml e.manifestSource

/-- Check the extension's vocabulary against its manifest: every operation it phrases, and
every operation a group stands for, is one the manifest emits; every field's fact is one the
manifest gives meaning to. A typo here would otherwise be a spec that allows nothing, or a
card that describes something that cannot happen. -/
def Extension.check (e : Extension) (m : Manifest) : Except String Unit := do
  let ops := Manifest.operations m
  for (o, _) in e.operations do
    if !ops.contains o then throw s!"the extension `{e.service}` phrases `{o}`, which its manifest never emits"
  for g in e.groups do
    for o in g.operations do
      if !ops.contains o then
        throw s!"the group `{g.name}` of `{e.service}` names `{o}`, which its manifest never emits"
  for f in e.fields do
    if !m.vocabulary.contains f.fact then
      throw s!"the field `{f.name}` of `{e.service}` reads `{f.fact}`, which its manifest never emits"

end Service
end Kleis
