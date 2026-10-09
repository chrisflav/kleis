# kleis in front of an agent orchestrator

[orchestra](https://github.com/chrisflav/orchestra) runs coding agents in
sandboxes.  With kleis in front of it, no sandbox holds a GitHub credential.
The agent uses the real `git` and `gh` against the real URLs; every program in
the sandbox has `HTTPS_PROXY` pointed here; and each job carries a token of its
own that orchestra minted for it, naming what the job may do.

## The pieces

- `config.toml`: the daemon's configuration.  It has an `orchestra` issuer,
  allowed to name the `orchestra-*` grants and state `task_*` facts, and
  `passthrough` for every host no manifest claims (the agent's model API,
  package managers).
- `grants/orchestra-github.toml`: everything a job may do on GitHub, in one
  grant.  It allows a request once, then chooses which credential it goes out
  on:
  1. a `credential_route` for the request's owner or repository, if the operator
     wrote one (`resources = ["acme/*"]` → acme's token);
  2. otherwise its rules:
     - the job's fork, repositories it created, and GraphQL go on the GitHub
       App's token;
     - the job's upstream goes on the operator's token;
  3. otherwise none: public dependencies are cloned and read anonymously.
- The GitHub manifest, `../github.toml`.

## The facts a job's token carries

Orchestra states these when it mints a token through `POST /.kleis/v1/tokens`:

```
task_fork("bot-org", "proj")         the fork the job works in
task_upstream("owner", "proj")       the repository it works for
task_issue(42)                       the issue or pull request it was launched from
task_tool("create_pr")               one per tool the job was granted
task_writable(true)                  unless the job is read-only
task_pr_labels(["orchestra"])        labels its pull requests carry
task_label_any(false)                true with label_issue: any label may be applied
task_org("bot-org")                  where it may create repositories
task_push_prefix("refs/heads/x/")    optional: where it may push
```

The grant is written over these facts, so one grant serves every job, and a
job's token says only which job it is.  The grant also requires
`issued_by("orchestra")`, so a token minted any other way reaches nothing.

To create a repository, a job with `create_repository` posts to
`/orgs/<task_org>/repos`.  Once GitHub answers 201, kleis remembers
`created_repository(org, name)` for that token, and the grant then lets the same
token push to the new repository.

## Setting it up

```sh
cp config.toml    "$KLEIS_HOME/config/config.toml"
cp ../github.toml "$KLEIS_HOME/config/services/"
cp grants/*.toml  "$KLEIS_HOME/config/grants/"

# The App's private key; its installation is looked up on the fork organisation.
kleis credential add github/orchestra-app --service github --provider github-app \
  --config '{"app_id": 123456, "owner": "bot-org"}' --secret @app.private-key.pem
# The token for the upstream: pull requests, comments, merges.
printf '%s' "$PAT" | kleis credential add github/orchestra-pat --service github --secret -

kleis issuer token orchestra --ttl 90d     # goes in orchestra's configuration
```

Per-owner tokens are a credential and a route each, added to the end of the
grant:

```toml
[[credential_route]]
resources  = ["acme/*"]
credential = "github/pat-acme"
```

Then add a `kleis` block to orchestra's `config.json`; see orchestra's
`docs/kleis.md`.

## What is not covered

- **GraphQL mutations** are refused.  `gh pr create`, `gh pr merge`,
  `gh issue comment` and `gh repo create` use them, so agents use `gh api`
  against the REST endpoints instead.
- **Label creation:** `label_issue` can add a label the repository does not
  define, and GitHub creates it.  A grant cannot ask the repository which labels
  exist.
- **App installations:** one per credential.  Forks in a second organisation
  need a second `github-app` credential and a route to it.
- **Scope on the upstream** is the repository, not the job's pull request: a job
  with `merge_pr` may merge any pull request there, and one with `create_pr`
  may add its pull request labels to any issue — the number of a pull request
  is not known until it exists.
- **GraphQL queries** go out on the App's token, so a job can read whatever the
  installation can, including other jobs' forks; the same was true of the
  installation token it used to hold.
