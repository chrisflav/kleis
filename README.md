# kleis

*κλείς, the key; κλειδοῦχος, the one who holds it.*  In a Greek temple the
kleidouchos held the key and opened the door for you; you never held the key.

A credential proxy. Somebody installs an access token for an external service
once; everybody else gets a *biscuit* that says, in datalog, what they may do
with it. They keep using `git`, `gh` and `curl` with the real URLs, and the
token itself never leaves this service.

> [!WARNING]
> **Experimental, LLM-generated, and not reviewed by a human.**
>
> This code was written by an LLM (Claude). No human has read it line by line.
> It handles credentials and terminates TLS; read it before trusting it with
> anything you would mind losing.

See [DESIGN.md](DESIGN.md) for why it is built the way it is.

## What it does

```sh
# The owner installs a token once, and says what may be done with it.
printf '%s' "$GITHUB_TOKEN" | kleis credential add github/chrisflav --service github --secret -

# A bearer gets a token that names a grant.
kleis token issue --grant ci-dev --bearer ci@build-07 --ttl 8h
```

With the proxy configured, the bearer runs ordinary commands against ordinary
URLs:

```sh
git push origin dev/feature   # allowed by the grant below
git push origin main          # 403, with the failed check quoted
```

The grant that decides this is a file:

```
check if allowed_operation($x);
check if repository("chrisflav", $r), ["kleis", "lean-biscuit"].contains($r);
reject if ref_update($ref), !$ref.starts_with("refs/heads/dev/");
allow if grant("ci-dev");
```

`reject if` rather than `check all` is not a style choice; see §4.3 of the
design for the two reasons.

`examples/` has three grants to copy from: `ci-dev` pushes to one branch prefix,
`read-only` clones and reads and cannot write, and `pr-approver` may approve
pull requests on one repository and do nothing else.

## Adding a service costs a file

Nothing in the Lean source knows that GitHub exists. A service is a manifest:
the hosts it owns, how its credential is attached, and routes turning requests
into datalog facts.

```toml
[[route]]
match = "POST github.com /{owner}/{repo%.git}/git-receive-pack"
emit  = ['operation("push")', 'repository($owner, $repo)']
```

The captures are substituted as *terms* into a template parsed once at load
time, so a repository named `a") or admin("x` is data rather than syntax.

Code is needed only for a new **wire format**, a new pure **extern**, or a new
**transport** — none of which is per-service. And even a new format has an
escape hatch: an `exec` decoder is a command that reads the body on standard
input and writes JSON on standard output. The test suite includes a CSV service
whose decoder is four lines of Python.

## Building

```sh
lake build          # the library, `kleis` and `kleisd`
lake test           # 213 checks: crypto vectors, decoders, policy, TLS
./scripts/integration.sh   # 32 checks: a real git push and clone through a daemon
```

Needs OpenSSL headers (`libssl-dev`) for the TLS shim, and `git`, `curl` and
`python3` for the integration test.

## Interception

Two modes, and the policy engine does not know which is in use.

**Rewrite** needs no certificate: git is configured to send real URLs to the
loopback with the origin in the path.

```sh
git config --global url."http://127.0.0.1:8080/https/github.com/".insteadOf "https://github.com/"
```

Pick one mode. They are mutually exclusive, and `kleis setup --mode rewrite` or
`--mode connect` unsets the other for you.

**CONNECT** is the real thing: `HTTPS_PROXY`, a certificate minted per SNI from
a local CA, TLS terminated and re-established to the origin with full
verification. `kleis setup` prints what to configure and where. The CA goes into
git's and curl's trust configuration, never into the system store.

```sh
eval "$(kleis setup --mode connect --token "$TOKEN")"
```

A client that pins certificates cannot be intercepted, and is not pretended
otherwise: it gets rewrite mode or a host-level grant.

The daemon verifies every origin, and checks at startup that its trust store
actually loaded rather than finding out on the first request. If your OpenSSL
was built somewhere other than where it runs, set `upstream_ca_file` in
`config.toml` to your system bundle.

## Commands

```
kleis setup            what to configure, and where
kleis service          list and inspect manifests
kleis grant            list and inspect grants
kleis credential       install, list and remove credentials
kleis token            issue, attenuate, inspect, list and revoke
kleis audit            tail the log, or verify its hash chain
kleis check            run a request against a policy without a proxy
kleisd                 the daemon
```

`kleis check` is the one worth knowing about. A grant is datalog, datalog is
easy to get subtly wrong, and this asks "would this be allowed" from a shell:

```sh
kleis check --token "$T" --method POST \
  --url https://api.github.com/repos/chrisflav/kleis/pulls/7/reviews \
  --content-type application/json --body '{"event":"APPROVE"}' --facts
```

## What is guaranteed, and how

Two things are enforced by the type checker rather than by review:

- **Nothing is forwarded without a decision.** The function that attaches a
  credential takes an `AuthorizedRequest`, and the only thing that constructs
  one is the authorizer.
- **A credential goes only where the manifest bound it.** `Secret` has a
  private field and one elimination, which checks the host — and is checked
  again after every redirect.

Attenuation is monotone by construction: a bearer can narrow a token offline,
and a block can only ever add checks. Revoking a token revokes every
attenuation derived from it.

The audit log is hash-chained and replayable: authorization is a pure function
of the facts, and the facts are in the record.

## Dependencies

One: [lean-biscuit](https://github.com/chrisflav/lean-biscuit), which brings
the token format, the datalog engine, and the curve arithmetic the local CA
signs with. The credential encryption (ChaCha20-Poly1305, PBKDF2), the JSON and
TOML readers, the HTTP stack and the X.509 encoder are written here, and
checked against published test vectors.
