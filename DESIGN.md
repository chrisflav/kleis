# auth

A credential proxy. Somebody installs an access token for an external service
once; everybody else gets a *biscuit* that says, in datalog, what they may do
with it. They keep using `git`, `gh`, `curl` and the real URLs — the token
itself never leaves this service.

The design goal that shapes everything below: **adding a new upstream service
must not require writing Lean.** A service is a file. What follows is mostly an
argument about where to draw that line so it is actually true, and what the
handful of things on the code side of it are.

## The three parties

- The **owner** holds an upstream credential and installs it here, together with
  *grants*: named datalog rules saying under what conditions the credential may
  be spent.
- The **bearer** holds a biscuit naming a grant. They can attenuate it offline —
  narrow it to one repository before handing it to a CI job — without asking
  anybody.
- The **upstream** sees an ordinary authenticated request and knows nothing
  about any of this.

```
 bearer                    authd                        upstream
   │                         │                             │
   │ git push (real URL,     │                             │
   │ proxy + biscuit)        │                             │
   ├────────────────────────▶│  extract facts              │
   │                         │  authorize (biscuit+grant)  │
   │                         │  bind credential            │
   │                         ├────────────────────────────▶│
   │                         │◀────────────────────────────┤
   │◀────────────────────────┤  audit                      │
```

## Non-goals

- Not a general egress firewall. It gates requests that spend *a credential it
  holds*; traffic it has no credential for is refused, not proxied anonymously.
- Not a secret manager for humans. Secrets go in, they do not come out.
- No attempt to defeat certificate pinning. A client that pins cannot be
  intercepted, and the answer is to use the non-intercepting mode for it.
- v1 is HTTP(S) only. `git+ssh` is left a seam, not a feature.

## What is data and what is code

This is the load-bearing table of the whole design.

| Concern | Where it lives | Adding one costs |
| --- | --- | --- |
| A service (github, gitlab, npm, AWS, an internal API) | a manifest file | a file |
| What a request *means* (push, approve-PR, publish) | manifest routes + datalog rules | a file |
| Who may do it | grant datalog + the bearer's biscuit | a file, or an offline attenuation |
| How the credential is attached | manifest injection template | a file |
| Where the credential comes from | credential provider | a file, if `exec` will do |
| A **wire format** (JSON, form, git pkt-line, protobuf) | a decoder | Lean |
| A **pure helper** datalog lacks (glob, CIDR, semver) | an extern | Lean |
| An **interception mode**, a transport | Lean | Lean |

So: any service that speaks HTTP with a body format we already decode needs no
code at all. A service speaking a format we have never seen needs one decoder —
once, for the *format*, not for the service. That is the honest boundary, and
`exec`-shaped escape hatches exist on both sides of it (§7, §5.4).

## 1. Request lifecycle

One pass, one seam per stage. Every stage is a pure function except the two ends.

```
  Listener ─▶ Identity ─▶ Interceptor ─▶ Decoder ─▶ Facts ─▶ Authorizer
                                                                │
                                            Audit ◀─────────── allow(i)/deny
                                                                │
                                       Upstream ◀── Credential binding
                                                                │
                                       Response ─▶ Facts ─▶ Transform ─▶ client
```

1. **Listener** accepts a connection (`Std.Internal.UV.TCP`, or a unix socket).
2. **Identity** resolves the bearer's biscuit from the connection (§4.1) and
   verifies its signature chain against our root key. No biscuit, no service.
3. **Interceptor** obtains a plaintext HTTP request (§6).
4. **Decoder** turns the body's leading bytes into a datalog value (§3.3).
5. **Facts** normalises request and body into a fact set (§3).
6. **Authorizer** assembles manifest ∪ grant ∪ token ∪ ambient facts and runs
   biscuit authorization (§4).
7. **Credential binding** is the *only* place a secret is read, and it consumes
   a value that only step 6 can produce (§5.3).
8. **Upstream** re-establishes real, fully verified TLS to the origin.
9. **Response** may itself be turned into facts and checked or transformed (§8).
10. **Audit** records the decision, the facts and the token's revocation ids so
    it can be replayed offline (§9.3).

## 2. The request model

Everything downstream of the interceptor sees one type, and it is deliberately
close to `LeanBiscuit.Datalog.Value` so that it needs no translation:

```lean
structure Request where
  method  : String
  scheme  : String
  host    : String
  port    : Nat
  path    : String
  segments: Array String
  query   : Array (String × String)
  headers : Array (String × String)   -- names lowercased
  body    : BodyRef                   -- streamed; see §8
```

`Value` already has integers, strings, dates, bytes, booleans, null, sets,
arrays and maps. A decoded JSON body *is* a `Value` with no lossy step, and
biscuit datalog can look inside it with `.get()`, `.contains()`, `.all()` and
`.any()`.

## 3. From bytes to facts

Three layers, in increasing order of how much the manifest gets to say.

### 3.1 Primitive facts — mechanical, always present

Emitted by the proxy for every request, with no manifest involvement:

```
request_method("POST");
request_host("github.com");
request_path("/chrisflav/auth.git/git-receive-pack");
request_segment(0, "chrisflav");
request_segment(1, "auth.git");
request_segment(2, "git-receive-pack");
request_header("content-type", "application/x-git-receive-pack-request");
request_query("per_page", "10");
request_size(4823117);
time(2026-08-28T21:00:00Z);
```

### 3.2 Body facts — the decoded body, flattened

The decoded body is emitted **twice**: once whole, as a single map/array term,
and once flattened to one fact per node, keyed by its path.

```
request_body({"title": "…", "base": "main"});
body(["title"], "Fix the thing");
body(["base"], "main");
body(["updates", 0, "ref"], "refs/heads/main");
body(["updates", 1, "ref"], "refs/heads/wip");
```

The flattening is what makes this work at all. Datalog cannot unnest an array
into facts, so `$body.get("updates")` gives you a value you can only test with a
closure — fine for "all of them satisfy a constant predicate", useless for "join
each of them against a rule". One fact per node fixes that: an array index
becomes an ordinary variable, and a rule can quantify over the elements.

```
ref_update($ref) <-
  body($p, $ref),
  $p.length() == 3, $p.get(0) == "updates", $p.get(2) == "ref";
```

Flattening is bounded by `maxBodyFacts` (default a few hundred, well under
biscuit's `maxFacts`). Exceeding it emits `body_truncated(true)` and *nothing
else from the body*, and the authorizer refuses on that fact (§4.2): a body too
big to reason about is a refusal rather than a blind spot.

A body has three states, not two, and the third was learned the hard way:

| Facts | Meaning |
| --- | --- |
| `body_opaque(false)` | a decoder read it, and the `body` facts are there |
| `body_opaque(true)`, `body_undecodable(false)` | no decoder was configured for its media type — nobody was asked to look |
| `body_opaque(true)`, `body_undecodable(true)` | a decoder *was* configured and could not read it |

The last is far more suspicious than the middle one: the manifest claimed to
know what those bytes are and they are not. The authorizer refuses on it
directly, because otherwise every `reject if` over body facts is vacuously
satisfied by a body nobody could parse — and `reject if` is exactly what a
grant should be using (§4.3).

### 3.3 Decoders — the first code-side seam

```lean
inductive Decoded where
  | need (atLeast : Nat)            -- undecided, feed me more bytes
  | done (value : Value) (consumed : Nat)
  | opaque                          -- structurally undecodable; body is bytes

structure Decoder where
  name    : String
  media   : Array String            -- content types it claims
  step    : Bytes → Bool → Decoded  -- bytes so far, is-eof
```

Decoders are **prefix** decoders, and that is a requirement, not an
optimisation. A `git push` is a 4 MB packfile whose ref updates sit in the first
few hundred bytes; a decoder that had to see the whole body would make the
proxy buffer every push. `step` gets a growing prefix and either decides or asks
for more, up to `maxDecodePrefix`; the remainder streams through untouched.

Shipped: `json`, `form`, `multipart` (headers only), `git-receive-pack`,
`git-upload-pack`, `none`. Two escape hatches so an unknown format need not
block anyone: `exec` (a subprocess reading a prefix on stdin and writing JSON on
stdout — pays a process per request, so it is for the long tail) and `opaque`,
which yields no body facts and therefore, given the `deny` preamble, no
authority to do anything body-dependent.

### 3.4 Routes — where new terms are minted

Datalog can filter but it cannot *compute a new term in a rule head*: externs
evaluate inside expressions, and expressions only decide whether a rule fires.
So `auth.git ↦ auth` cannot be a rule. Routes cover exactly that gap, and are
the only bespoke syntax in the system:

```toml
[[route]]
match = "POST github.com /{owner}/{repo}.git/git-receive-pack"
emit  = ['operation("push")', 'repository($owner, $repo)']

[[route]]
match = "PUT api.github.com /repos/{owner}/{repo}/pulls/{number:int}/merge"
emit  = ['operation("merge_pr")', 'repository($owner, $repo)', 'pull_request($number)']
```

Segment captures are `{name}`, typed with `:int` or `:date`, suffix-trimmed with
`{repo%.git}`, and `{rest*}` swallows the tail. Captures may also come from
headers, query parameters and body paths (`{ref<-body:["updates",0,"ref"]}`).
A route that matches emits its facts with the captures substituted. No route
matching a request is not an error — it simply means the semantic facts are
absent, and the grant's checks fail closed.

### 3.5 Manifest rules — plain biscuit datalog

Everything else the manifest wants to say is ordinary datalog over §3.1–3.4,
parsed by `LeanBiscuit.Parser`, and therefore already tested, printable and
diffable:

```
protected_ref($r) <- ref_update($r), $r.starts_with("refs/heads/release/");
deletes_ref($r)   <- body($p, $new), $p.get(2) == "new", $new == "0000000000000000000000000000000000000000";
```

## 4. Authorization

### 4.1 Identifying the bearer

The biscuit rides on the *hop*, never on the request that goes upstream:

- `Proxy-Authorization: Bearer <biscuit>` — works for `git` (`http.proxy` with
  credentials, `http.extraHeader`), `curl`, and anything honouring `HTTPS_PROXY`.
- a per-session unix socket, bearer identified by peer uid — for a sandbox that
  should not be able to read its own token at all.
- a per-bearer ephemeral listener port, for tools that cannot set proxy auth.

Whichever it is, `Proxy-Authorization` and any client-supplied `Authorization`
are stripped before the request is forwarded.

### 4.2 What each party contributes

| Contributor | Kind | Meaning |
| --- | --- | --- |
| service manifest | facts, rules | what the request *is* |
| grant (owner) | facts, checks, policies | what may be done with the credential |
| biscuit authority (issued by us) | facts, checks | which grant, which bearer, expiry |
| biscuit blocks (bearer, offline) | checks | self-imposed narrowing |
| ambient | facts | time, client identity, request id |

Biscuit's evaluation order gives us the property we want for free: every check
from every block must pass, and blocks can only ever *add* checks. Attenuation
is therefore monotone by construction — a derived token can never authorize
something its parent would not (§10.3).

### The guards the authorizer adds

Two **checks**, not policies. A check is order-independent — it must pass
whichever `allow` matched — whereas a policy appended after the grant's would
never be reached once an earlier `allow` had matched:

```
check if body_truncated(false);     // a body too large to flatten
check if body_undecodable(false);   // a body a configured decoder could not read
```

And one policy, appended last, so that a grant whose policies all fail to match
denies rather than falling through:

```
deny if true;
```

### 4.3 Writing a grant: four things that will bite

All four were found by running the worked example against real `git`, and all
four are in the files under `examples/` for that reason.

**A push is two requests.** `git push` first asks for the ref advertisement
(`GET /info/refs?service=git-receive-pack`) and only then sends the pack. A
grant allowing just `operation("push")` refuses the first one, and the push
fails before it starts. Datalog has no `or`, so the disjunction is a pair of
rules:

```
allowed_operation("push") <- operation("push");
allowed_operation("discover") <-
  operation("discover"), discover_service("git-receive-pack");
check if allowed_operation($x);
```

**`check all` requires at least one match.** It is the obvious way to write
"every ref update is under `dev/`", and it is wrong here: the ref advertisement
carries no ref updates at all, so `check all` refuses it. `reject if` is the
right tool — vacuously satisfied when there is nothing to reject, and it still
catches the mixed push, which is the hole `check all` was reached for in the
first place:

```
reject if ref_update($ref), !$ref.starts_with("refs/heads/dev/");
```

**`reject if` is vacuous on a body nobody could read.** That is exactly what
`body_undecodable` and its guard (§4.2) exist for. Without it, sending garbage
under a `git-receive-pack` content type would produce no `ref_update` facts,
and the rejection above would pass.

**Comments in datalog are `//`, not `#`.** The datalog lives inside a TOML
multi-line string, so TOML never sees it; `#` reaches the datalog parser and is
a syntax error rather than a comment. Relatedly, a TOML key written after a
`[[route]]` header belongs to *that table* — document-level settings such as
`max_body_facts` go at the top of the file, above every header.

### 4.4 Externs — the second code-side seam

`ExternFunc := Value → Option Value → Except String Value`, registered by the
host, callable as `$x.extern::name($y)`. They are pure filters, they never bind
variables, and the set is fixed at build time — which is precisely why the
standard set must be *service-independent*: `glob`, `cidr_contains`,
`semver_satisfies`, `path_normalize`, `json_pointer`, `hmac_verify`. A service
manifest that wants a service-specific extern is a smell and a review comment;
it should be a route or a rule.

Externs are also the natural place to say "no" to expensive things: they are
called once per candidate binding, so anything unbounded belongs in a decoder.

### 4.5 Revocation and freshness

`Biscuit.revocationIdentifiers` gives one id per block. Every id is checked
against a revocation set before authorization — revoking a parent kills every
attenuation of it, which is the behaviour you want when a laptop is lost.
Grants carry a maximum token lifetime, enforced as an authority-block check
(`check if time($t), $t < <expiry>`) rather than trusted to the server clock
alone.

## 5. Credentials

### 5.1 The secret type

```lean
structure Secret where
  private bytes : ByteArray
```

No `ToString`, no `Repr`, no `ToJson`. The only elimination is §5.3. This is not
a proof, it is a type — but it is the kind of type that makes the proof short.

### 5.2 Providers

A provider turns stored material into a live secret. The manifest names one:

| Provider | For |
| --- | --- |
| `static` | a PAT, an API key |
| `oauth2` | refresh-token flows, cached until expiry |
| `github-app` | installation tokens, minted per repository, ~1 h |
| `exec` | run a command, read the token from stdout |

`exec` is why "adding a provider costs a file, if `exec` will do" is in the
table: any credential you can obtain with a shell command needs no Lean. The
others exist because they are common enough to be worth caching and refreshing
properly.

Where the provider can mint a *narrower* upstream credential (a GitHub App
installation token scoped to one repository, an STS session with a policy), the
grant may ask it to, so the credential that leaves the building is already
attenuated even if the proxy is later bypassed. Defence in depth: the datalog is
the fine-grained control, the minted scope is the coarse one.

### 5.3 Injection and confinement

```toml
[credential]
provider = "github-app"
hosts    = ["github.com", "api.github.com", "codeload.github.com"]

[[credential.inject]]
kind     = "header"
name     = "Authorization"
template = "Bearer {{secret}}"

strip = ["authorization", "proxy-authorization", "cookie"]
```

`hosts` is a hard binding, checked again after every redirect. A redirect to a
host outside the list is followed, if at all, *without* the credential. This is
the rule that stops a crafted redirect from exfiltrating the token.

The signature of the only function that reads a secret:

```lean
def bind (r : AuthorizedRequest) (s : Secret) : Except BindError Model.Request
```

`AuthorizedRequest` has one constructor, private to `Auth.Policy.Authorize` and
produced only on `allow`; `Secret` has a private field and lives in the same
module as `bind`, because `private` in Lean is per-module and putting the
elimination anywhere else would mean exposing the field. Forwarding a
credential without a decision is not a bug to be avoided by review; it is a
program that does not compile.

## 6. Interception

Three modes behind one `Interceptor` seam. The policy engine does not know which
is in use, and the choice is deployment, not architecture.

### 6.1 Rewrite (no TLS, ship this first)

`git config url."http://127.0.0.1:8080/gh/".insteadOf "https://github.com/"`.
The bearer types real URLs; git rewrites them. The proxy speaks plain HTTP on
the loopback and real TLS upstream. Works today with no TLS server, exercises
every other stage, and is genuinely adequate for `git`. Its limits are honest
ones: it depends on client config support, and `gh` needs `GH_HOST` gymnastics.

### 6.2 CONNECT with interception (the real thing)

`HTTPS_PROXY=http://127.0.0.1:8080`. On `CONNECT host:443` we mint a leaf
certificate for the SNI name from a local CA, terminate TLS, and open a properly
verified TLS connection upstream. `auth setup` installs the CA where the tools
look — `http.sslCAInfo`, `GIT_SSL_CAINFO`, `SSL_CERT_FILE`, `NODE_EXTRA_CA_CERTS`
— and only there, never in the system store.

The CA and leaf minting can be pure Lean: `LeanBiscuit.Crypto` already has
Ed25519, secp256r1 and SHA-2, so what is missing is a DER writer and a small
X.509 profile. That is a contained, testable piece of work and it keeps the
certificate path inside the library that is already written to be verified.

The *transport* is the part Lean does not have. Plan: a `Auth.Net.Stream`
interface with `read`/`write`/`close`, implemented by plain TCP and by a TLS
backend behind a small C FFI shim over OpenSSL — the shape `orchestra` already
uses for `UnixSocket.c` and `Signal.c`. Everything above `Stream` is testable
over plain sockets and provable without mentioning TLS at all. Writing TLS 1.3
in Lean is a fine future project and this interface is what would make it a drop-in.

### 6.3 Transparent

Netfilter redirect plus SNI, for sandboxes that must not be able to opt out.
Same code path as 6.2 minus the `CONNECT`.

### 6.4 Modes that cannot work

A client that pins certificates cannot be intercepted, and pretending otherwise
would be a footgun. Such a client gets mode 6.1 or a coarse, connection-level
grant with no body inspection. The manifest says which modes a service supports.

## 7. Service manifests

One file per service, in `$AUTH_HOME/config/services`. The complete example is
`examples/github.toml`; the shape is:

```toml
name  = "github"
hosts = ["github.com", "api.github.com", "codeload.github.com"]
modes = ["rewrite", "connect"]

max_body_facts = 512      # document-level settings go first -- see below

datalog = '''
ref_update($ref) <- body($p, $ref), ...      # §3.5, facts and rules only
'''

[credential]              # §5.3
[[credential.inject]]
[[decoder]]               # bind a media type to a decoder
[[route]]                 # §3.4
```

The ordering is not cosmetic. In TOML a key written after a `[[route]]` header
belongs to *that table*, so a `max_body_facts` at the bottom of the file
silently becomes a setting on the last route and the document-level default
stays where it was. Everything that belongs to the document goes above the
first header.

Manifests are data, pinned like any other dependency. A manifest can add facts
and rules, and it can *never* add a `check` or an `allow` — both are load
errors, not warnings, so a manifest that would escalate cannot sit in a
directory waiting for the right request. Only the grant decides. That asymmetry
is what makes it safe to install a manifest you did not write.

## 8. Streaming, responses and transforms

- Requests stream. The decoder sees a prefix; the decision is made before the
  body is relayed; the rest is copied through without buffering.
- Responses may be turned into facts (`response_status`, `response_header`,
  `response_body` with the same flattening) and checked. A check that fails
  after the request has gone upstream cannot un-send it, so response checks are
  for *disclosure* control, not for authorization — and the manifest must mark
  a route as `response_gated` to make the proxy buffer rather than stream.
- **Transforms** are the seam for "you may fetch, but you may only see branch
  X": rewriting the ref advertisement of `GET /info/refs`. Declarative, tiny,
  and deliberately postponed past v1, but the seam is placed now because
  retrofitting it into a streaming relay is painful.

## 9. State

### 9.1 What is stored

Flat files under a data dir, `0600`, in the style of `orchestra`, behind a
`Store` interface so a database can replace it later:

- **credentials** — encrypted at rest; key from the OS keyring, a passphrase, or
  a key file.
- **grants** — name, credential, service, datalog source, max token lifetime.
- **issued tokens** — revocation ids, label, expiry, issuing grant. Not the
  token; we do not need it and should not have it.
- **revocations** — an append-only set of revocation ids.

### 9.2 Root keys

The service is the biscuit root. The root private key is generated on first run
and never leaves the host. `rootKeyId` is set so the key can be rotated with
both keys live during the overlap.

### 9.3 Audit

One append-only record per decision, hash-chained with SHA-256 (already in
`LeanBiscuit.Crypto`): timestamp, revocation ids, service, route, the *complete*
fact set, the manifest and grant versions, the matched policy index, the
upstream status. Because authorization is pure and total, an audit record
replays to the same decision — "why was this allowed" is a question with an
answer, offline, months later.

Secrets never enter the log; the record names the credential, never its value.

## 10. Properties worth verifying

The point of doing this in Lean rather than in Go is that some of these become
theorems rather than intentions.

1. **Fail-closed, structurally.** `Credential.bind` takes an
   `AuthorizedRequest`, whose only constructor is private to the authorizer,
   and `Proxy.sendUpstream` is only ever reached with what `bind` returned.
   Enforced by the type checker, not by review.
2. **Credential confinement.** `Secret` is eliminated only by `bind`, and `bind`
   requires `r.host ∈ manifest.credential.hosts`. Statement: no execution
   forwards secret bytes to a host outside that list — including after redirects.
3. **Attenuation is monotone.** If `t'` is `t` with blocks appended, then for
   every request `r`, `authorize t' r = allow → authorize t r = allow`. This is
   the property the whole offline-attenuation story rests on, it follows from
   biscuit's evaluation order, and `lean-biscuit` being pure, total and
   `sorry`-free is what makes it stateable at all.
4. **Manifests cannot escalate.** Installing a manifest never turns a `deny`
   into an `allow`: manifests contribute only facts and rules, and the appended
   `deny if true` is last. Provable by induction over the policy list.
5. **Extraction is faithful.** For every decoder, the flattened `body` facts
   agree with the decoded value at every path — a round-trip property, checked
   per decoder, ideally proved for `json`.
6. **Determinism.** Authorization is a pure function of (token, facts, grant,
   manifest). Hence §9.3 replays.

1, 2 and 6 are design constraints to be honoured from the first commit; 3 and 4
are the theorems worth actually proving; 5 is a property test that can grow into
a proof for the formats that deserve one.

## 11. Module layout

```
Auth/Util/{Bytes,Str,Json,Toml,Base64}   text, bytes, and the two config formats
Auth/Crypto/{ChaCha20,Poly1305,Aead}     credential encryption at rest
Auth/Http/{Message,Reader,Writer,Chunked}
Auth/Model/Request                       the normalized request
Auth/Wire/{Decoder,Json,Form,Git,Registry,Exec}
Auth/Facts/{Primitive,Flatten,Route}
Auth/Service/{Manifest,Registry}
Auth/Policy/{Externs,Grant,Authorize}
Auth/Credential/{Secret,Store,Provider}
Auth/Token/{Issue,Revocation}
Auth/Net/{Stream,Resolve,Socket,Tls,TlsStream,ClientHello,Client}
Auth/Ca/{Der,X509,Mint}                  the local certificate authority
Auth/{Dirs,Store,Config,Audit}
Auth/Proxy/{Context,Body,Forward,Session,Listener}
Auth/Cli                                 `auth`
ffi/{Tls,Net}.c                          OpenSSL, and getaddrinfo
```

About eight and a half thousand lines of Lean and three hundred of C, against
one dependency: `lean-biscuit`.

Everything from `Auth/Util` through `Auth/Policy` is pure and total — no `IO`,
no `partial` — which is what §10.6 rests on. The `partial` definitions are all
under `Auth/Net` and `Auth/Proxy`, where the loops genuinely do not terminate:
an accept loop has no measure that decreases.

The binaries are split the way `orchestra` splits `orchestra` and `orchestrad`:
`authd` holds the credentials and is the only process that ever decrypts one;
`auth` is everything a person types, and can be run by anybody.

The C is the smallest surface that could work. `Tls.c` is a byte transform over
two memory BIOs — it never sees a socket, so everything above `Auth.Net.Stream`
is testable over plain buffers, and a TLS implementation in Lean would drop in
without a line changing elsewhere. `Net.c` is `getaddrinfo`, which Lean's
networking does not have.

## 12. Worked example: push only to `dev/*`

**Manifest** (`services/github.toml`), written once, by anyone:

```toml
name  = "github"
hosts = ["github.com", "api.github.com", "codeload.github.com"]

[credential]
provider = "github-app"
hosts    = ["github.com", "api.github.com", "codeload.github.com"]
[[credential.inject]]
kind     = "header"
name     = "Authorization"
template = "Bearer {{secret}}"

[[decoder]]
media   = ["application/x-git-receive-pack-request"]
decoder = "git-receive-pack"

[[route]]
match = "POST github.com /{owner}/{repo%.git}/git-receive-pack"
emit  = ['operation("push")', 'repository($owner, $repo)']

[[route]]
match = "GET github.com /{owner}/{repo%.git}/info/refs"
capture = { service = "query:service" }
emit  = ['operation("discover")', 'repository($owner, $repo)',
         'discover_service($service)']

[[route]]
match = "PUT api.github.com /repos/{owner}/{repo}/pulls/{number:int}/merge"
emit  = ['operation("merge_pr")', 'repository($owner, $repo)', 'pull_request($number)']

datalog = """
ref_update($ref) <-
  body($p, $ref), $p.length() == 3, $p.get(0) == "updates", $p.get(2) == "ref";
force_push($ref) <-
  body($p, true), $p.length() == 3, $p.get(0) == "updates", $p.get(2) == "force";
"""
```

**Grant** (`examples/ci-dev.toml`), written by the owner:

```
credential   = "github/chrisflav"
max_lifetime = "24h"
datalog = """
// A push is two requests: the ref advertisement, then the pack.  Allowing only
// `operation("push")` refuses the first, and the push never starts.
allowed_operation("push") <- operation("push");
allowed_operation("discover") <-
  operation("discover"), discover_service("git-receive-pack");

check if allowed_operation($x);
check if repository("chrisflav", $r), ["auth", "lean-biscuit"].contains($r);

// `reject if`, not `check all`.  Both catch the mixed push -- one good ref must
// not carry a bad one through -- but `check all` also requires at least one
// match, so it would refuse the ref advertisement, which carries no ref
// updates at all.
reject if ref_update($ref), !$ref.starts_with("refs/heads/dev/");
reject if deletes_ref($any);

allow if grant("ci-dev");
"""
```

The mixed push is the case that matters: a push carrying ten ref updates must
have *every* one inside `dev/`, not merely one. Getting that wrong is the
classic hole in this kind of gateway. The first attempt at this file used
`check all` for it, which is correct about the mixed push and refuses the ref
advertisement — so the push failed before it began. That is why §4.3 exists.

**Token**, issued by `auth token issue --grant ci-dev --ttl 8h`, authority block:

```
grant("ci-dev");
bearer("ci@build-07");
check if time($t), $t < 2026-08-29T05:00:00Z;
```

**Attenuation**, by the bearer, offline, with no server involved:

```
$ auth token attenuate --check 'check if repository("chrisflav", "auth")'
```

**Request.** `git push origin dev/feature`. Git asks for the ref advertisement
first, which `allowed_operation("discover")` covers. Then it POSTs the pack.
The proxy emits `request_method("POST")`, `request_host("github.com")`, the
segments, and — from the first 178 bytes of a request whose packfile follows
them — `body(["updates", 0, "ref"], "refs/heads/dev/feature")`. The route emits
`operation("push")` and `repository("chrisflav", "auth")`. Every check passes,
`allow if grant("ci-dev")` matches, the credential is attached, and the packfile
streams through without ever being buffered.

`git push origin main` produces `ref_update("refs/heads/main")`, the `reject if`
fires, and the bearer gets `403` — the packfile is never relayed. When the
refusal lands on the ref advertisement, git prints the quoted check as a
`remote:` message; when it lands on the POST, git prints only the status, and
the reason is in the response's `X-Auth-Request-Id` and in the audit log.

All of the above is what `scripts/integration.sh` actually runs, against a real
`git` and a real daemon, in both interception modes.

## 13. What is built

M1 through M4 of the original plan are implemented and exercised by
`scripts/integration.sh` against a real `git` and a real daemon.

| | State |
| --- | --- |
| Rewrite mode (§6.1) | done |
| `CONNECT` interception (§6.2) | done — local CA, per-SNI leaves, TLS both sides |
| Transparent mode (§6.3) | not implemented; the same code path minus `CONNECT` |
| Decoders: `json`, `form`, `multipart`, `git-receive-pack`, `git-upload-pack` | done |
| `exec` decoder | done — a CSV service with a four-line Python decoder is in the tests |
| Primitive facts, body flattening, routes, manifest rules (§3) | done |
| Grants, checks, policies, externs, revocation (§4) | done |
| `Secret`, host confinement, injection (§5) | done |
| Providers: `static`, `exec`, `oauth2`, `github-app` | done |
| Token issue / attenuate / inspect / revoke (§9) | done |
| Hash-chained audit log with `auth audit verify` (§9.3) | done |
| Streaming request and response relay (§8) | done |
| Response facts and transforms (§8) | **not implemented**; `response_gated` is parsed and the seam is in place |
| Connection reuse | not implemented: one request per upstream connection |
| The proofs (§10.3, §10.4, §10.5) | **not attempted**; see below |

The cryptography is checked against published vectors — RFC 8439 for
ChaCha20-Poly1305, RFC 7914 for PBKDF2 — and every certificate the CA mints is
read back by OpenSSL, which is what verifies the hand-written DER.

### What the properties of §10 actually stand on

1. **Fail-closed** and 2. **credential confinement** are *enforced by types*, as
   designed: `Policy.AuthorizedRequest` has a private constructor, and
   `Credential.bind` is the only elimination of `Secret` that reaches a
   request. Neither is a proof; both are compile errors.
3. **Attenuation is monotone** and 4. **manifests cannot escalate** are
   **tested, not proved**. A manifest containing a `check` or a `policy` is a
   load error, and the tests exercise a parent token, an attenuation of it, and
   a request each way — but the general statement is not formalised.
5. **Extraction is faithful** is tested per decoder, not proved.
6. **Determinism** holds by construction: everything from `Auth.Model` through
   `Auth.Policy` is pure and total, with no `IO` and no `partial`. The `partial`
   definitions are all in the daemon layer, where the loops genuinely do not
   terminate.

Proving 3 and 4 is the remaining piece of the original plan, and the code is
arranged for it: the decision is a pure function of its inputs.

## 14. Still to do

**Response transforms.** The seam is placed — a route may declare itself
`response_gated`, and `Manifest.gatesResponse` reports it — but nothing acts on
it yet. This is what "you may fetch, but only see branch X" needs, and it means
rewriting the ref advertisement of `GET /info/refs`.

**Connection reuse.** Each request opens a connection to the origin and closes
it. Correct, and slower than it should be for a clone.

**Transparent interception.** Netfilter redirect plus SNI, for sandboxes that
must not be able to opt out. The open question below about identity is the
reason it is not done rather than the plumbing.

**`git+ssh`.** The same policy engine over a different transport, with the proxy
as an SSH server holding the real key. Large, separate, and the fact vocabulary
is deliberately neutral enough to accept it later.

## 15. Open questions

- **Where does the biscuit come from in mode 6.3?** Transparent interception has
  no `CONNECT` to carry `Proxy-Authorization`. Per-uid or per-namespace binding
  is the obvious answer and it makes the sandbox story stronger, but it means
  identity is ambient rather than presented.
- **Are body facts the right cap?** `maxBodyFacts` trades expressiveness for a
  bounded world. A large JSON body that is *mostly* irrelevant will truncate;
  manifests may need to declare which body paths to flatten, at the cost of one
  more thing in the manifest.
- **Grant composition.** Two grants over one credential: union of policies, or
  must the bearer pick one per request? Union is friendlier and much harder to
  reason about. Leaning towards one grant per token.
- **Third-party blocks.** Biscuit supports blocks signed by another key, so a
  service could attest facts about the bearer (a CI system vouching for the
  commit being pushed). Attractive and entirely out of scope for v1, but the
  authorizer should not close the door on it.
- **`git+ssh`.** The same policy engine over a different transport, with the
  proxy as an SSH server holding the real key. Large, separate, and worth
  keeping the fact vocabulary neutral enough to accept later.
- **Idempotency of retries.** A client retrying a `merge_pr` after a timeout is
  authorized twice. Deduplicating on a request id is easy; deciding whether that
  is our job is not.
