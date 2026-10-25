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
- `grants/orchestra-reviewer-github.toml`: what a review job may do on GitHub,
  which is read.
- `specs/`: what a job made from a spec may do (`worker`, `secretary`,
  `reviewer`), and `diff-reviewer-poster`, which is not a job's; see
  [Reviews](#reviews-for-diff-reviewer) below.
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

# The App's private key. Its installation is looked up on the owner of each
# repository a request is about (`per_owner`): orchestra works on a repository
# directly when the App is installed there, and forks it into bot-org when not.
# `owner` is for requests about no repository, such as GraphQL.
kleis credential add github/orchestra-app --service github --provider github-app \
  --config '{"app_id": 123456, "owner": "bot-org", "per_owner": true}' --secret @app.private-key.pem
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

## Reviews for diff-reviewer

[diff-reviewer](https://github.com/chrisflav/diff-reviewer) reviews pull
requests with agents and posts what its operator approves.  It queues a job on
orchestra per pull request, as an API client; the agent reads the job and the
diff from the platform and submits its review there, with the
`diff-reviewer agent` command.  The platform posts reviews to GitHub as
Christian: for a repository in `direct` mode it posts a submission at once, as
a COMMENT review only, and an approving or change-requesting review only when
a person clicks Post.  That is enforced by the platform, not by kleis, which
cannot tell those requests apart and allows every review event.  Two specs,
and the agent token and the PAT are not interchangeable:

- `specs/reviewer.kleis`, the job's.  On the platform (the `diff-reviewer`
  extension's account): read the job and the diff, and submit a review, only
  for the pull request the job is for — `repository` equal to its
  `task_upstream`, `pull` equal to its `task_issue`.  Nothing else on the
  platform is reachable: no `/api/v1/`, no login.  On GitHub, the grant
  `orchestra-reviewer-github`: clone, fetch and read, GraphQL queries, and no
  write at all — no push, even to the job's fork, no pull request, review,
  comment or label.  Its GraphQL queries go out on the App's token, as a
  worker's do, so a review job can read whatever the installation can see.
- `specs/diff-reviewer-poster.kleis`, the platform's own.  On
  `github/chrisflav`: read the repositories in its list through the REST API,
  review their pull requests and comment on their diffs.  Reading is every GET
  and HEAD under a listed repository's `/repos/{owner}/{name}/…` — contents,
  commits, issues, workflow runs — not only its pull requests.  Every request
  must name a listed repository, so any other repository is refused, and so is
  everything about none — `/user`, `/search`, `/rate_limit`, GraphQL — which
  would reach the rest of what the token can see.  It is not an issuer's spec:
  orchestra cannot derive it.

Why the job does not get `orchestra-github` with `read_only`: that grant takes
pushing away from a read-only job (`task_writable`), but its other writes turn
on tools, so a read-only job given `create_pr` or `comment` could still open
pull requests and review.  And with its fork equal to its upstream — a
repository the App is installed on — the upstream counts as its fork, where a
pull request needs no head from anywhere.  The review grant has no write rule
to inherit.

The credentials go in before the specs: a spec naming a credential that is not
there does not load.  kleisd refuses to start on it, and a running one keeps
the configuration it had, so copying the specs first only logs a failed reload.

```sh
# The platform's agent token (its DIFF_REVIEWER_AGENT_TOKEN_FILE), bound to the
# platform's host; the account the reviewer spec names.
kleis credential add diff-reviewer/agent --service diff-reviewer \
  --hosts reviews.example --secret @agent.token
# Christian's token, which approved reviews are posted with.
printf '%s' "$PAT" | kleis credential add github/chrisflav --service github --secret -

cp specs/reviewer.kleis specs/diff-reviewer-poster.kleis "$KLEIS_HOME/config/specs/"

# The platform's token. It goes in the platform's HTTPS_PROXY
# (http://kleis:<token>@<kleis>:8080), with `kleis ca` in its CA bundle; its
# DIFF_REVIEWER_GITHUB_TOKEN_FILE holds the placeholder `kleis`.
kleis token issue --spec diff-reviewer-poster --bearer diff-reviewer --ttl 90d
```

`config.toml` enables the `diff-reviewer` extension, lets the `orchestra`
issuer derive `reviewer`, and raises `[limits] max_decode_prefix` to 4 MiB.
A body is refused, not relayed unread, when it is larger than the smaller of
that and its manifest's `max_decode_prefix`, or becomes more facts than the
manifest's `max_body_facts`.  The GitHub and diff-reviewer manifests set
4 MiB and 4096, which admits a review of some 500 inline comments, about
2 MiB; with the default 64 KiB a review of a few dozen comments is refused,
both a job's submission and the platform's post.  On the orchestra side the platform is an API client,
`<config>/clients/diff-reviewer.json`, and the client names the spec:

```json
{"token": "{{diff_reviewer_token}}", "read_only": true, "kleis_spec": "reviewer",
 "queue_policy": {"repos": ["chrisflav/kleis"], "max_budget": 3.0}}
```

Each job the platform queues carries `upstream` and `issue_number`, which
orchestra states as `task_upstream` and `task_issue`; the sandbox gets
`~/.config/diff-reviewer/agent.json` from `/.kleis/v1/setup`, with the
placeholder token `kleis`.  Its `url` is `https://` and the account's host,
with no port: an account's hosts are names, so the platform has to be served
on 443.  The repositories are in three places that must
agree: the platform's registered repositories, the client's
`queue_policy.repos`, and the list in `diff-reviewer-poster.kleis`
(`reviewed([...])`), which kleis rereads when it changes.

## What is not covered

- **GraphQL mutations** are refused.  `gh pr create`, `gh pr merge`,
  `gh issue comment` and `gh repo create` use them, so agents use `gh api`
  against the REST endpoints instead.
- **Label creation:** `label_issue` can add a label the repository does not
  define, and GitHub creates it.  A grant cannot ask the repository which labels
  exist.
- **App installations** are looked up per owner with `per_owner`. Without it a
  credential reaches one account, and a second needs a credential and a route.
- **Scope on the upstream** is the repository, not the job's pull request: a job
  with `merge_pr` may merge any pull request there, and one with `create_pr`
  may add its pull request labels to any issue — the number of a pull request
  is not known until it exists.
- **GraphQL queries** go out on the App's token, so a job can read whatever the
  installation can, including other jobs' forks; the same was true of the
  installation token it used to hold.
- **A review job's card** has the GitHub extension's phrases for its task facts
  — "your fork is …; push there", "open pull requests there" — which are written
  for a worker.  The grant quoted under them allows neither.
- **The poster's list** is matched exactly: `reviewed(["chrisflav/kleis"])`
  does not admit `/repos/ChrisFlav/kleis`, which GitHub would.  That refuses;
  it never admits more.
- **Large bodies are slow to decide.**  A body at the GitHub manifest's 4096
  facts takes some four seconds to decide, and any GitHub bearer may send one.
