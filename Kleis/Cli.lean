import Kleis

/-!
# The command line

`kleis` is a client: it reads and writes the files the daemon reads, and it
never holds a listening socket.  The split follows `kleisd`'s: the daemon is the
process that holds credentials in memory, and everything a person types is a
separate program that can be run without one.

The parser is hand written rather than taken from a library, so that the
package keeps `lean-biscuit`'s property of having exactly one dependency.  The
grammar is small enough that this costs less than it sounds.
-/

namespace Kleis
namespace Cli

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- Parsed arguments: the positional words and the `--name value` options. -/
structure Args where
  /-- Words that are not options. -/
  positional : List String
  /-- Options, in the order given. -/
  options : List (String × String)
  /-- Flags given without a value. -/
  flags : List String

/-- Split an argument vector.

An option is `--name value` unless the next word also starts with `--`, in
which case it is a flag.  That rule is why `--json` and `--ttl 8h` can live
side by side without a schema. -/
def parseArgs (argv : List String) : Args :=
  let rec go (l : List String) (pos : List String) (opts : List (String × String))
      (flags : List String) : Args :=
    match l with
    | [] => { positional := pos.reverse, options := opts.reverse, flags := flags.reverse }
    | a :: rest =>
      if a.startsWith "--" then
        let name := Str.stripPrefix a "--"
        match rest with
        | v :: more =>
          if v.startsWith "--" then go (v :: more) pos opts (name :: flags)
          else go more pos ((name, v) :: opts) flags
        | [] => go [] pos opts (name :: flags)
      else go rest (a :: pos) opts flags
  termination_by l.length
  go argv [] [] []

/-- The value of an option. -/
def Args.opt? (a : Args) (name : String) : Option String :=
  (a.options.find? fun (k, _) => k == name).map (·.2)

/-- Every value given for an option that may be repeated, in order. -/
def Args.opts (a : Args) (name : String) : List String :=
  a.options.filterMap fun (k, v) => if k == name then some v else none

/-- The value of an option, or a default. -/
def Args.optD (a : Args) (name value : String) : String := (a.opt? name).getD value

/-- Was this flag given? -/
def Args.flag (a : Args) (name : String) : Bool :=
  a.flags.contains name || (a.opt? name).isSome && (a.opt? name) == some "true"

/-- The positional word at an index. -/
def Args.at? (a : Args) (i : Nat) : Option String := a.positional[i]?

/-- Fail with a message. -/
def die (message : String) : IO α := do
  let h ← IO.getStderr
  h.putStrLn s!"kleis: {message}"
  h.flush
  IO.Process.exit 1

/-- Print a line. -/
def say (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-- Read a value that may be given inline, as `@file`, or on standard input. -/
def readValue (given : Option String) : IO String := do
  match given with
  | some v =>
    if v.startsWith "@" then IO.FS.readFile (Str.stripPrefix v "@")
    else if v == "-" then do pure (← (← IO.getStdin).readToEnd)
    else pure v
  | none => do pure (← (← IO.getStdin).readToEnd)

/-- The same, as bytes.

Request bodies are not text.  A `git-receive-pack` body is pkt-lines followed
by a packfile, and reading it as UTF-8 fails outright — which would make
`kleis check` useless for exactly the bodies it is most needed for. -/
def readBytes (given : Option String) : IO Bytes := do
  match given with
  | some v =>
    if v.startsWith "@" then IO.FS.readBinFile (Str.stripPrefix v "@")
    else if v == "-" then do pure (← (← IO.getStdin).readBinToEnd)
    else pure (Bytes.ofString v)
  | none => do pure (← (← IO.getStdin).readBinToEnd)

/-! ## Commands -/

/-- `kleis root-key` — the public key a verifier needs. -/
def cmdRootKey : IO Unit := do
  say (← Token.rootPublicKey).print

/-- `kleis ca` — the local certificate authority. -/
def cmdCa (args : Args) : IO Unit := do
  let root ← Ca.loadOrCreateRoot
  if args.flag "pem" then say root.pem
  else say ((← Dirs.ca) / "ca.crt").toString

/-- `kleis setup` — what to put where, so the tools trust and use the proxy.

One mode at a time, and the other mode's settings are unset.  The two are
mutually exclusive and combining them fails in a way that takes a while to
read: `insteadOf` rewrites the URL to the proxy, `http.proxy` then sends *that*
through the proxy, and the daemon is asked to fetch from itself.  An earlier
version of this command printed both configurations one after the other under
comment headers, which is an invitation to paste the lot. -/
def cmdSetup (args : Args) : IO Unit := do
  let config ← loadConfig
  let _ ← Ca.loadOrCreateRoot
  let caPath := ((← Dirs.ca) / "ca.crt").toString
  let listen := s!"{config.listenHost}:{config.listenPort}"
  let token := args.optD "token" "<your-biscuit>"
  let registry ← Service.Registry.load
  let mode ← match args.opt? "mode" with
    | some "connect" => pure Mode.connect
    | some "rewrite" => pure Mode.rewrite
    | some m => die s!"--mode is `connect` or `rewrite`, not `{m}`"
    | none => pure (if config.mode == .rewrite then Mode.rewrite else Mode.connect)

  say "# Run this through a shell, or paste it.  Everything for the other mode"
  say "# is unset first: the two cannot both be configured."
  say ""

  match mode with
  | .rewrite | .both =>
    say "# --- rewrite mode: no certificate, git sends real URLs to the loopback."
    say "git config --global --unset http.proxy || true"
    say "git config --global --unset http.proxyAuthMethod || true"
    say "unset HTTPS_PROXY HTTP_PROXY"
    say ""
    for m in registry.manifests do
      for host in m.hosts do
        say s!"git config --global url.\"http://{listen}/https/{host}/\".insteadOf \"https://{host}/\""
    say s!"git config --global http.extraHeader \"Proxy-Authorization: Bearer {token}\""
  | .connect =>
    say "# --- intercepting mode: real URLs through CONNECT, needs the CA trusted."
    for m in registry.manifests do
      for host in m.hosts do
        say s!"git config --global --remove-section url.\"http://{listen}/https/{host}/\" || true"
    say "git config --global --unset http.extraHeader || true"
    say ""
    say s!"export HTTPS_PROXY=http://kleis:{token}@{listen}"
    say s!"export HTTP_PROXY=http://kleis:{token}@{listen}"
    say s!"export SSL_CERT_FILE={caPath}"
    say s!"export GIT_SSL_CAINFO={caPath}"
    say s!"export NODE_EXTRA_CA_CERTS={caPath}"
    say ""
    say s!"git config --global http.proxy http://kleis:{token}@{listen}"
    say "# `proxyAuthMethod` matters: git's default probes for a scheme, and curl"
    say "# does not understand Bearer for a proxy."
    say "git config --global http.proxyAuthMethod basic"
    say s!"git config --global http.sslCAInfo {caPath}"

  say ""
  say s!"# The CA lives at {caPath}.  Keep it there: it is read on every request,"
  say "# and a copy under a temporary directory stops working when that is cleaned."

/-- `kleis service list|show` -/
def cmdService (args : Args) : IO Unit := do
  let registry ← Service.Registry.load
  match args.at? 1 with
  | some "show" =>
    let some name := args.at? 2 | die "usage: kleis service show <name>"
    let some m := registry.manifest? name | die s!"no such service `{name}`"
    say s!"name    {m.name}"
    say s!"hosts   {String.intercalate ", " m.hosts}"
    say s!"modes   {String.intercalate ", " m.modes}"
    say s!"version {m.version}"
    say s!"credential provider {m.credential.provider}, bound to {String.intercalate ", " m.credential.hosts}"
    say s!"routes  {m.routes.length}"
    say s!"rules   {m.rules.length}"
  | _ =>
    for m in registry.manifests do
      say s!"{m.name}\t{String.intercalate ", " m.hosts}"

/-- `kleis grant list|show` -/
def cmdGrant (args : Args) : IO Unit := do
  let registry ← Service.Registry.load
  match args.at? 1 with
  | some "show" =>
    let some name := args.at? 2 | die "usage: kleis grant show <name>"
    let some g := registry.grant? name | die s!"no such grant `{name}`"
    say g.source
  | _ =>
    for g in registry.grants do
      say s!"{g.name}\t{g.service}\t{g.credentialLabel}\tmax {g.maxLifetime}s"

/-- `kleis credential add|list|remove` -/
def cmdCredential (args : Args) : IO Unit := do
  match args.at? 1 with
  | some "add" =>
    let some name := args.at? 2 | die "usage: kleis credential add <name> --service <s>"
    let service ← match args.opt? "service" with
      | some s => pure s
      | none => die "a credential needs --service"
    let provider := args.optD "provider" "static"
    let config ← match args.opt? "config" with
      | none => pure (Json.obj [])
      | some c => do
        let text ← readValue (some c)
        match Json.parse text with
        | .ok j => pure j
        | .error e => die s!"--config is not JSON: {e}"
    let material ← readValue (args.opt? "secret")
    if Str.trim material |>.isEmpty then die "the credential material is empty"
    Credential.save name service provider config (Credential.Secret.ofString material)
    say s!"installed `{name}` for {service} via {provider}"
  | some "remove" =>
    let some name := args.at? 2 | die "usage: kleis credential remove <name>"
    if ← Credential.remove name then say s!"removed `{name}`"
    else die s!"no such credential `{name}`"
  | _ =>
    for r in ← Credential.list do
      say s!"{r.name}\t{r.service}\t{r.provider}"

/-- `kleis token issue|attenuate|inspect|list|revoke` -/
def cmdToken (args : Args) : IO Unit := do
  match args.at? 1 with
  | some "issue" =>
    let registry ← Service.Registry.load
    -- `--grant a --grant b` and `--grant a,b` both name two, tried in that order.
    let grants := (args.opts "grant").flatMap fun g =>
      (g.splitOn ",").map Str.trim |>.filter (!·.isEmpty)
    if grants.isEmpty then die "issuing a token needs --grant"
    let bearer := args.optD "bearer" "unnamed"
    let ttl ← match Policy.parseDuration? (args.optD "ttl" "8h") with
      | some t => pure t
      | none => die "--ttl is a duration such as `8h`"
    let facts ← (args.opts "fact").mapM fun src =>
      match Token.factOfSource src with
      | .ok f => pure f
      | .error e => die e
    match ← Token.mint registry { grants, bearer, ttl, facts } with
    | .error e => die e
    | .ok (token, _) => say (Token.print token)
  | some "attenuate" =>
    let text ← readValue (args.opt? "token")
    let root ← Token.rootPublicKey
    let token ← match Token.parse text root with
      | .ok t => pure t
      | .error e => die e
    let check ← match args.opt? "check" with
      | some c => pure c
      | none => die "attenuating needs --check '<datalog>'"
    let ephemeral ← match PrivateKey.ofBytes .ed25519 (← Store.randomBytes 32) with
      | .ok k => pure k
      | .error e => die e.toString
    match Token.attenuate token check ephemeral with
    | .error e => die e
    | .ok t => say (Token.print t)
  | some "inspect" =>
    let text ← readValue (args.opt? "token")
    let root ← Token.rootPublicKey
    match Token.parse text root with
    | .error e => die e
    | .ok token => do
      say s!"grants  {(", ".intercalate (Token.grantsOf token))}"
      if let some i := Token.issuerOf? token then say s!"issuer  {i}"
      say s!"bearer  {(Token.bearerOf? token).getD "-"}"
      say s!"blocks  {Biscuit.blockCount token}"
      say s!"sealed  {Biscuit.isSealed token}"
      say "revocation ids:"
      for id in Biscuit.revocationIdentifiers token do
        say s!"  {Bytes.toHex id}"
      say ""
      for (block, i) in token.blocks.zipIdx do
        let symbols := if block.externalKey.isSome && i != 0 then block.symbols else token.symbols
        say (if i == 0 then "// authority" else s!"// block {i}")
        for f in block.facts do
          say (Datalog.printFact symbols f ++ ";")
        for c in block.checks do
          say (Datalog.printCheck symbols c ++ ";")
  | some "revoke" =>
    let some needle := args.at? 2 | die "usage: kleis token revoke <revocation-id>"
    let issued ← Token.listIssued
    match Token.findIssued? issued needle with
    | some r => do
      Token.revoke r.revocationIds
      say s!"revoked the token issued to `{r.bearer}` under `{r.grantLabel}`"
      say "every attenuation derived from it is revoked with it"
    | none => do
      Token.revoke [needle]
      say s!"revoked `{needle}` (no issue record found; the identifier is listed anyway)"
  | _ =>
    let now ← Store.now
    for r in ← Token.listIssued do
      let state := if r.expires < now then "expired" else "live"
      say s!"{(r.revocationIds.headD "")}\t{r.grantLabel}\t{r.bearer}\t{(r.issuedBy.getD "-")}\t{state}"

/-- `kleis issuer list|token <name>` — the programs that may ask the daemon for
tokens, and the credential one of them presents when it does.

An issuer is configured in `config.toml`; this only mints its credential, a
biscuit carrying `issuer(name)` and no grant.  It spends nothing by itself, and
it is revoked like any other token. -/
def cmdIssuer (args : Args) : IO Unit := do
  let config ← loadConfig
  match args.at? 1 with
  | some "token" =>
    let some name := args.at? 2 | die "usage: kleis issuer token <name> [--ttl 90d]"
    if (config.issuer? name).isNone then
      die s!"no issuer `{name}` is configured in config.toml"
    let ttl ← match Policy.parseDuration? (args.optD "ttl" "90d") with
      | some t => pure t
      | none => die "--ttl is a duration such as `90d`"
    let registry ← Service.Registry.load
    match ← Token.mint registry { grants := [], bearer := s!"issuer:{name}", ttl
                                  issuer := some name } with
    | .error e => die e
    | .ok (token, _) => say (Token.print token)
  | _ =>
    for i in config.issuers do
      say s!"{i.name}\tgrants {", ".intercalate i.grants}\tfacts {", ".intercalate i.facts}\tmax {i.maxTtl}s"

/-- `kleis audit verify|tail` -/
def cmdAudit (args : Args) : IO Unit := do
  match args.at? 1 with
  | some "verify" =>
    let (count, broken) ← auditVerify
    match broken with
    | none => say s!"{count} records, chain intact"
    | some i => do
      say s!"{count} records read; the chain breaks at record {i}"
      IO.Process.exit 1
  | _ =>
    let n := ((args.optD "n" "20").toNat?).getD 20
    match ← Store.read? (← Dirs.auditLog) with
    | none => say "no audit log yet"
    | some text =>
      let lines := (text.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
      for line in lines.drop (lines.length - min n lines.length) do
        match Json.parse line with
        | .error _ => say line
        | .ok j =>
          let r := (j.field? "record").getD (.obj [])
          let allowed := if (r.bool? "allowed").getD false then "allow" else "DENY "
          say s!"{(r.str? "time").getD (toString ((r.int? "time").getD 0))} {allowed} {(r.str? "method").getD ""} {(r.str? "url").getD ""} — {(r.str? "outcome").getD ""}"

/-- `kleis check` — run a request against the policy without a proxy.

The most useful thing in this program.  A grant is datalog, and datalog is easy
to get subtly wrong; being able to ask "would this be allowed" from a shell,
with the body in a file, turns writing a policy into something with a feedback
loop shorter than a `git push`. -/
def cmdCheck (args : Args) : IO Unit := do
  let registry ← Service.Registry.load
  let url ← match args.opt? "url" with
    | some u => pure u
    | none => die "checking needs --url"
  let method := (args.optD "method" "GET").toUpper
  let body ← match args.opt? "body" with
    | none => pure ByteArray.empty
    | some b => readBytes (some b)
  let contentType := args.opt? "content-type"
  let text ← readValue (args.opt? "token")
  let root ← Token.rootPublicKey
  let token ← match Token.parse text root with
    | .ok t => pure t
    | .error e => die s!"the token was not accepted: {e}"
  -- Build the wire request the proxy would have seen.
  let headers : Http.Headers :=
    #[] |> (fun h => match contentType with
              | some c => Http.Headers.set h "content-type" c
              | none => h)
        |> (fun h => if body.size == 0 then h
                     else Http.Headers.set h "content-length" (toString body.size))
  let wire : Http.Request := {
    method, target := url, version := "HTTP/1.1", headers
    framing := if body.size == 0 then .empty else .length body.size }
  let bare ← match Model.Request.ofWire wire "https" none body true with
    | .ok r => pure r
    | .error e => die e
  let some manifest := registry.forHost? bare.host
    | die s!"no service manifest claims `{bare.host}`"
  let grants ← match Policy.candidates registry token manifest bare.host with
    | .ok gs => pure gs
    | .error r => die r.toString
  let decoder := manifest.decoderFor contentType bare
  let decoded ← Wire.runDecoder decoder body true
  let revocations ← Token.loadRevocations
  let now ← Store.now
  let choice := Policy.choose grants fun grant => {
    request := bare
    body := Policy.Body.classify decoder.configured (body.size != 0) decoded
    manifest, grant, token, revoked := revocations.ids, now
    clientIp := args.optD "client-ip" "127.0.0.1", requestId := "check" }
  let outcome := choice.outcome
  if args.flag "facts" then
    say "// facts"
    for f in outcome.facts do say f
    say ""
  match outcome.decision with
  | .allow i => say s!"ALLOW (grant {choice.grant.name}, policy {i})"
  | .deny _ _ => do
    say s!"DENY {choice.reason}"
    IO.Process.exit 1

/-- Usage text. -/
def usage : String :=
"kleis — a credential proxy

usage:
  kleis setup [--mode connect|rewrite] [--token <biscuit>]
                                     what to configure, and where
  kleis root-key                      the biscuit root public key
  kleis ca [--pem]                    the local certificate authority

  kleis service list | show <name>
  kleis grant   list | show <name>

  kleis credential add <name> --service <s> [--provider static|exec|oauth2|github-app]
                             [--config <json|@file>] [--secret <value|@file|->]
  kleis credential list | remove <name>

  kleis token issue --grant <g>[,<g>…] [--bearer <b>] [--ttl 8h]
                    [--fact '<datalog fact>']…
  kleis token attenuate --check '<datalog>' [--token <t|@file|->]
  kleis token inspect [--token <t|@file|->]
  kleis token list | revoke <revocation-id>

  kleis issuer list | token <name> [--ttl 90d]

  kleis audit tail [--n 20] | verify

  kleis check --url <url> [--method M] [--body <text|@file>]
             [--content-type <t>] [--token <t|@file|->] [--facts]

the daemon is `kleisd`."

/-- Dispatch. -/
def main (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  match args.at? 0 with
  | none => do say usage; return 0
  | some command =>
    try
      match command with
      | "setup" => cmdSetup args
      | "root-key" => cmdRootKey
      | "ca" => cmdCa args
      | "service" => cmdService args
      | "grant" => cmdGrant args
      | "credential" => cmdCredential args
      | "token" => cmdToken args
      | "issuer" => cmdIssuer args
      | "audit" => cmdAudit args
      | "check" => cmdCheck args
      | "help" | "--help" => say usage
      | other => do
        let h ← IO.getStderr
        h.putStrLn s!"kleis: unknown command `{other}`"
        h.putStrLn usage
        return 1
      return 0
    catch e => do
      let h ← IO.getStderr
      h.putStrLn s!"kleis: {e}"
      return 1

end Cli
end Kleis
