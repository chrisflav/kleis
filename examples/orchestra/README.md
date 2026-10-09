# kleis in front of an agent orchestrator

[orchestra](https://github.com/chrisflav/orchestra) runs coding agents in
sandboxes.  With kleis in front of it, no sandbox holds a GitHub credential: the
agent uses the real `git` and `gh` against the real URLs, every program in the
sandbox has `HTTPS_PROXY` pointed here, and each job carries a token of its own
that orchestra minted for it, naming what the job may do.

## The pieces

- `config.toml` — the daemon's configuration: an `orchestra` issuer allowed to
  name the `orchestra-*` grants and state `task_*` facts, and `passthrough` for
  every host no manifest claims (the agent's model API, package managers).
- `grants/` — what a job may do, in the order its token names them:

  | grant | credential | for |
  | --- | --- | --- |
  | `orchestra-fork` | the GitHub App | fetch, push to, read and open pull requests on the job's fork; GraphQL queries |
  | `orchestra-upstream` | a person's token | read and fetch the upstream; open pull requests on it from the fork; comment on the job's own issue; merge |
  | `orchestra-triage` | a person's token | label any issue on the upstream, for jobs with `label_issue` |
  | `orchestra-public` | none | clone and read anything public, anonymously |

- The GitHub manifest, `../github.toml`.

## The facts a job's token carries

Orchestra states these when it mints a token, through `POST /.kleis/v1/tokens`:

```
task_fork("bot-org", "proj")         the fork the job works in
task_upstream("owner", "proj")       the repository it works for
task_issue(42)                       the issue or pull request it was launched from
task_tool("create_pr")               one per tool the job was granted
task_writable(true)                  unless the job is read-only
task_pr_labels(["orchestra"])        labels its pull requests carry
task_push_prefix("refs/heads/x/")    optional: where it may push
```

The grants are written over these, so one set of grants serves every job and a
job's token says only which job it is.  `issued_by("orchestra")` is required
by every grant, so a token minted any other way reaches nothing.

## Setting it up

```sh
cp config.toml   "$KLEIS_HOME/config/config.toml"
cp ../github.toml "$KLEIS_HOME/config/services/"
cp grants/*.toml "$KLEIS_HOME/config/grants/"

# The App's private key; its installation is looked up on the fork organisation.
kleis credential add github/orchestra-app --service github --provider github-app \
  --config '{"app_id": 123456, "owner": "bot-org"}' --secret @app.private-key.pem
# The token comments and pull requests on the upstream are made with.
printf '%s' "$PAT" | kleis credential add github/orchestra-pat --service github --secret -

kleis issuer token orchestra --ttl 90d     # goes in orchestra's configuration
kleis ca                                   # the CA orchestra's sandboxes trust
```

Then `kleis` in orchestra's `config.json` — see orchestra's `docs/kleis.md`.

## What is not covered

- GraphQL mutations are refused outright: `gh pr create`, `gh pr merge` and
  `gh issue comment` use them.  Agents use `gh api` against the REST endpoints
  instead, which the grants can read.
- `label_issue` can add a label the repository does not define (GitHub creates
  it); a grant cannot ask the repository which labels exist.
- One App installation per credential.  Forks in a second organisation need a
  second `github-app` credential and a grant naming it.
