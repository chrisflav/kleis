#!/usr/bin/env bash
# End to end: a real `curl` and a real `git push` through a running daemon.
#
# Everything happens in a temporary KLEIS_HOME, against a local origin, over
# plain HTTP in rewrite mode -- so the test needs no certificate installed
# anywhere and touches nothing of the invoking user's.
set -uo pipefail

# `cd` is guarded everywhere below.  Without that, a `cd` into a directory a
# failed step never created leaves the script running in the repository it was
# launched from -- where the `git config` and `git commit` further down are
# then applied to somebody's real work.  This happened.
enter() { cd "$1" || { printf 'kleis-test: cannot enter %s\n' "$1" >&2; exit 1; }; }

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"
export KLEIS_HOME="$WORK/home"
export KLEIS_STORE_KEY="$(printf '%064d' 7)"
KLEIS="$ROOT/.lake/build/bin/kleis"
KLEISD="$ROOT/.lake/build/bin/kleisd"

PASS=0; FAIL=0
ok()   { PASS=$((PASS+1)); printf '  ok   %s\n' "$1"; }
bad()  { FAIL=$((FAIL+1)); printf '  FAIL %s\n' "$1"; [ $# -gt 1 ] && printf '       %s\n' "$2"; }
check(){ if [ "$1" = "0" ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

cleanup() {
  [ -n "${DECL_PID:-}" ] && kill "$DECL_PID" 2>/dev/null
  [ -n "${KLEISD_PID:-}" ] && kill "$KLEISD_PID" 2>/dev/null
  [ -n "${ORIGIN_PID:-}" ] && kill "$ORIGIN_PID" 2>/dev/null
  [ -n "${TLS_ORIGIN_PID:-}" ] && kill "$TLS_ORIGIN_PID" 2>/dev/null
  [ -n "${KEEP_WORK:-}" ] && echo "work kept in $WORK" || rm -rf "$WORK"
}
trap cleanup EXIT

free_port() { python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1]);s.close()'; }

ORIGIN_PORT="$(free_port)"
KLEIS_PORT="$(free_port)"

mkdir -p "$KLEIS_HOME/config/services" "$KLEIS_HOME/config/grants" "$WORK/repos"

# ---------------------------------------------------------------- the origin
git init --quiet --bare "$WORK/repos/demo.git"
git -C "$WORK/repos/demo.git" config http.receivepack true
python3 "$ROOT/scripts/origin.py" "$ORIGIN_PORT" "$WORK/repos" &
ORIGIN_PID=$!
for _ in $(seq 50); do
  curl -s -o /dev/null "http://127.0.0.1:$ORIGIN_PORT/echo" && break
  sleep 0.1
done

# ---------------------------------------------------------------- config
cat > "$KLEIS_HOME/config/config.toml" <<EOF
listen = "127.0.0.1:$KLEIS_PORT"
mode = "rewrite"
EOF

cat > "$KLEIS_HOME/config/services/demo.toml" <<'EOF'
name  = "demo"
hosts = ["127.0.0.1"]
modes = ["rewrite"]

datalog = '''
ref_update($ref) <-
  body($p, $ref), $p.length() == 3, $p.get(0) == "updates", $p.get(2) == "ref";
'''

[credential]
provider = "static"
hosts    = ["127.0.0.1"]
# The test origin speaks plain HTTP; a real service's credential never would.
allow_plaintext = true
strip    = ["cookie"]

[[credential.inject]]
kind     = "header"
name     = "Authorization"
template = "Bearer {{secret}}"

[[decoder]]
media   = ["application/x-git-receive-pack-request"]
decoder = "git-receive-pack"

[[route]]
match = "POST 127.0.0.1 /{repo%.git}/git-receive-pack"
emit  = ['operation("push")', 'repository($repo)']

[[route]]
match = "GET 127.0.0.1 /{repo%.git}/info/refs"
capture = { service = "query:service" }
emit  = ['operation("discover")', 'repository($repo)', 'discover_service($service)']

[[route]]
match = "POST 127.0.0.1 /{repo%.git}/git-upload-pack"
emit  = ['operation("fetch")', 'repository($repo)']

[[route]]
match = "GET|POST 127.0.0.1 /echo"
emit  = ['operation("echo")']

[[route]]
match = "POST 127.0.0.1 /echo/make/{name}"
emit  = ['operation("make")', 'thing($name)']
on_success = ['made($name)']

[[route]]
match = "GET 127.0.0.1 /echo/thing/{name}"
emit  = ['operation("get_thing")', 'thing($name)']
EOF

cat > "$KLEIS_HOME/config/grants/dev.toml" <<'EOF'
name         = "dev-only"
service      = "demo"
credential   = "demo/token"
max_lifetime = "24h"

datalog = '''
allowed_operation("push") <- operation("push");
allowed_operation("discover") <-
  operation("discover"), discover_service("git-receive-pack");
check if allowed_operation($x);
reject if ref_update($ref), !$ref.starts_with("refs/heads/dev/");
allow if grant("dev-only");
'''
EOF

cat > "$KLEIS_HOME/config/grants/read.toml" <<'EOF'
name         = "read-only"
service      = "demo"
credential   = "demo/token"
max_lifetime = "1h"

datalog = '''
allowed_operation("discover") <-
  operation("discover"), discover_service("git-upload-pack");
allowed_operation("fetch") <- operation("fetch");
check if allowed_operation($x);
allow if grant("read-only");
'''
EOF

cat > "$KLEIS_HOME/config/grants/echo.toml" <<'EOF'
name         = "echo-only"
service      = "demo"
credential   = "demo/token"
max_lifetime = "1h"

datalog = '''
check if operation("echo");
allow if grant("echo-only");
'''
EOF

echo "== configuration"
printf 'upstream-secret-42' | "$KLEIS" credential add demo/token --service demo --secret - >/dev/null
check $? "install a credential"
"$KLEISD" --check >/dev/null 2>&1
check $? "the daemon loads its configuration"

DEV_TOKEN="$("$KLEIS" token issue --grant dev-only --bearer ci@test --ttl 1h)"
check $? "issue a token for the push grant"
ECHO_TOKEN="$("$KLEIS" token issue --grant echo-only --bearer ci@test --ttl 1h)"
check $? "issue a token for the echo grant"
READ_TOKEN="$("$KLEIS" token issue --grant read-only --bearer ci@test --ttl 1h)"
check $? "issue a token for the read-only grant"

# ---------------------------------------------------------------- the daemon
"$KLEISD" > "$WORK/kleisd.log" 2>&1 &
KLEISD_PID=$!
for _ in $(seq 50); do
  curl -s -o /dev/null "http://127.0.0.1:$KLEIS_PORT/" && break
  sleep 0.1
done

BASE="http://127.0.0.1:$KLEIS_PORT/http/127.0.0.1:$ORIGIN_PORT"

echo
echo "== the credential"
OUT="$(curl -s -H "Proxy-Authorization: Bearer $ECHO_TOKEN" "$BASE/echo")"
echo "$OUT" | grep -q '"authorization": "Bearer upstream-secret-42"'
check $? "the origin receives the credential" "$OUT"
echo "$OUT" | grep -q 'proxy-authorization'
if [ $? -eq 0 ]; then bad "the biscuit is not forwarded upstream" "$OUT"; else ok "the biscuit is not forwarded upstream"; fi

# A client that sends its own Authorization must not have it reach the origin.
OUT="$(curl -s -H "Proxy-Authorization: Bearer $ECHO_TOKEN" -H "Authorization: Bearer client-supplied" "$BASE/echo")"
echo "$OUT" | grep -q 'client-supplied'
if [ $? -eq 0 ]; then bad "a client-supplied Authorization is replaced" "$OUT"; else ok "a client-supplied Authorization is replaced"; fi

echo
echo "== refusals"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' "$BASE/echo")"
[ "$CODE" = "407" ]; check $? "no token gets 407" "got $CODE"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Proxy-Authorization: Bearer not-a-token" "$BASE/echo")"
[ "$CODE" = "407" ]; check $? "a malformed token gets 407" "got $CODE"
# The echo grant only allows `operation("echo")`, so a git path is refused.
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Proxy-Authorization: Bearer $ECHO_TOKEN" "$BASE/demo.git/info/refs?service=git-upload-pack")"
[ "$CODE" = "403" ]; check $? "a request outside the grant gets 403" "got $CODE"
grep -q 'check if operation' "$WORK/body"
check $? "and the refusal quotes the failed check" "$(cat "$WORK/body")"

echo
echo "== a real git push"
export GIT_CONFIG_GLOBAL="$WORK/gitconfig"
export GIT_CONFIG_NOSYSTEM=1
git config --global user.email dev@test
git config --global user.name dev
git config --global protocol.version 2
git config --global "url.$BASE/.insteadOf" "http://127.0.0.1:$ORIGIN_PORT/"
git config --global http.extraHeader "Proxy-Authorization: Bearer $DEV_TOKEN"

git init --quiet "$WORK/clone"
enter "$WORK/clone"
git remote add origin "http://127.0.0.1:$ORIGIN_PORT/demo.git"
echo hello > file.txt
git add file.txt
git commit --quiet -m "first"

git branch -M dev/feature
git push --quiet origin dev/feature > "$WORK/push-dev.log" 2>&1
check $? "push to dev/feature succeeds" "$(cat "$WORK/push-dev.log")"
# The bare repo's HEAD still names a branch nothing was ever pushed to, so a
# clone of it would check out an empty tree.
git -C "$WORK/repos/demo.git" symbolic-ref HEAD refs/heads/dev/feature

git branch -M main
git push origin main > "$WORK/push-main.log" 2>&1
if [ $? -ne 0 ]; then ok "push to main is refused"; else bad "push to main is refused" "it succeeded"; fi
# git surfaces a `remote:` message when the *discovery* is refused, but for the
# RPC POST it prints only the status.  The reason is in the response header's
# request id and in the audit log, which is where an operator looks.
grep -q '403' "$WORK/push-main.log"
check $? "and git reports the refusal" "$(cat "$WORK/push-main.log")"
grep -q 'refs/heads/dev/' "$KLEIS_HOME/data/audit.log"
check $? "and the audit log records the failed check"

# The mixed case: one good ref must not carry a bad one through.
git branch dev/second
git push origin dev/second main > "$WORK/push-mixed.log" 2>&1
if [ $? -ne 0 ]; then ok "a mixed push is refused"; else bad "a mixed push is refused" "it succeeded"; fi

enter "$ROOT"

echo
echo "== a real git clone with a read-only token"
git config --global --unset-all http.extraHeader
git config --global http.extraHeader "Proxy-Authorization: Bearer $READ_TOKEN"
rm -rf "$WORK/readclone"
git clone --quiet "http://127.0.0.1:$ORIGIN_PORT/demo.git" "$WORK/readclone" > "$WORK/clone.log" 2>&1
check $? "clone succeeds with a read-only token" "$(cat "$WORK/clone.log")"
[ -f "$WORK/readclone/file.txt" ]
check $? "and the working tree has the pushed file"

# The same token must not be able to write.
enter "$WORK/readclone"
git config user.email r@test
git config user.name r
echo more >> file.txt
git commit --quiet -am "should not land"
git push origin HEAD:refs/heads/dev/nope > "$WORK/readpush.log" 2>&1
if [ $? -ne 0 ]; then ok "and the same token cannot push"; else bad "and the same token cannot push" "it succeeded"; fi
# Refused by policy, not by git having nothing to send.
grep -q '403' "$WORK/readpush.log"
check $? "refused by the proxy rather than locally" "$(cat "$WORK/readpush.log")"
enter "$ROOT"

# ...while the push token cannot clone, which is the other half of the split.
git config --global --unset-all http.extraHeader
git config --global http.extraHeader "Proxy-Authorization: Bearer $DEV_TOKEN"
rm -rf "$WORK/devclone"
git clone --quiet "http://127.0.0.1:$ORIGIN_PORT/demo.git" "$WORK/devclone" > "$WORK/devclone.log" 2>&1
if [ $? -ne 0 ]; then ok "and a push-only token cannot clone"; else bad "and a push-only token cannot clone" "it succeeded"; fi
git config --global --unset-all http.extraHeader
git config --global http.extraHeader "Proxy-Authorization: Bearer $DEV_TOKEN"

echo
echo "== revocation"
REVOKE_TOKEN="$("$KLEIS" token issue --grant echo-only --bearer ci@revoke --ttl 1h)"
CODE="$(curl -s -o /dev/null -w '%{http_code}' -H "Proxy-Authorization: Bearer $REVOKE_TOKEN" "$BASE/echo")"
[ "$CODE" = "200" ]; check $? "a token that will be revoked works first" "got $CODE"
REV="$("$KLEIS" token inspect --token "$REVOKE_TOKEN" | sed -n '/revocation ids:/{n;p}' | tr -d ' ')"
"$KLEIS" token revoke "$REV" >/dev/null
check $? "revoke a token"
# The daemon notices the revocation list changed within its few-second poll.
for _ in $(seq 20); do
  CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Proxy-Authorization: Bearer $REVOKE_TOKEN" "$BASE/echo")"
  [ "$CODE" = "403" ] && break
  sleep 0.5
done
[ "$CODE" = "403" ] && grep -q revoked "$WORK/body"; check $? "a revoked token is refused" "got $CODE: $(cat "$WORK/body")"

echo
echo "== interception: real https URLs through CONNECT"
# A separate origin, over TLS, with a certificate of its own.  The proxy
# verifies it the way it would verify a real one; git verifies the proxy's
# minted leaf against the local CA.
TLS_PORT="$(free_port)"
TLS_KLEIS_PORT="$(free_port)"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 1 \
  -keyout "$WORK/origin.key" -out "$WORK/origin.crt" \
  -subj "/CN=127.0.0.1" -addext "subjectAltName=IP:127.0.0.1" >/dev/null 2>&1
check $? "mint a certificate for the TLS origin"

git init --quiet --bare "$WORK/repos/tls.git"
git -C "$WORK/repos/tls.git" config http.receivepack true
python3 "$ROOT/scripts/origin.py" "$TLS_PORT" "$WORK/repos" "$WORK/origin.crt" "$WORK/origin.key" &
TLS_ORIGIN_PID=$!
sleep 1

cat > "$KLEIS_HOME/config/config.toml" <<EOF
listen = "127.0.0.1:$TLS_KLEIS_PORT"
mode = "connect"
upstream_ca_file = "$WORK/origin.crt"
EOF

kill "$KLEISD_PID" 2>/dev/null; wait "$KLEISD_PID" 2>/dev/null
"$KLEISD" > "$WORK/kleisd-tls.log" 2>&1 &
KLEISD_PID=$!
for _ in $(seq 50); do
  curl -s -o /dev/null "http://127.0.0.1:$TLS_KLEIS_PORT/" && break
  sleep 0.1
done

CA="$("$KLEIS" ca)"
check $? "the local CA is available"
TLS_TOKEN="$("$KLEIS" token issue --grant dev-only --bearer ci@tls --ttl 1h)"
TLS_ECHO_TOKEN="$("$KLEIS" token issue --grant echo-only --bearer ci@tls --ttl 1h)"

# curl, with real URLs, through the intercepting proxy.
OUT="$(curl -s --proxy "http://kleis:$TLS_ECHO_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic --cacert "$CA" "https://127.0.0.1:$TLS_PORT/echo" 2>&1)"
echo "$OUT" | grep -q '"authorization": "Bearer upstream-secret-42"'
check $? "an intercepted https request carries the credential" "$OUT"

# and a real git push, over https, with the URL git was given untouched.
git config --global --unset-all "url.$BASE/.insteadOf" 2>/dev/null
git config --global --unset-all http.extraHeader 2>/dev/null
git config --global http.proxy "http://kleis:$TLS_TOKEN@127.0.0.1:$TLS_KLEIS_PORT"
git config --global http.proxyAuthMethod basic
git config --global http.sslCAInfo "$CA"

git init --quiet "$WORK/tlsclone"
enter "$WORK/tlsclone"
git remote add origin "https://127.0.0.1:$TLS_PORT/tls.git"
echo tls > file.txt
git add file.txt
git commit --quiet -m "over tls"
git branch -M dev/tls
git push origin dev/tls > "$WORK/push-tls.log" 2>&1
check $? "push over https through CONNECT succeeds" "$(cat "$WORK/push-tls.log")"

git branch -M main
git push origin main > "$WORK/push-tls-main.log" 2>&1
if [ $? -ne 0 ]; then ok "and main is still refused over https"; else bad "and main is still refused over https" "it succeeded"; fi
enter "$ROOT"

echo
echo "== connection reuse"
# Two requests in one curl: the second goes on the same connection to the
# proxy, through the same tunnel, when the first ended where its framing said.
OUT="$(curl -s -o /dev/null -o /dev/null --proxy "http://kleis:$TLS_ECHO_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic --cacert "$CA" -w '%{num_connects}\n' \
  "https://127.0.0.1:$TLS_PORT/echo" "https://127.0.0.1:$TLS_PORT/echo" 2>&1)"
[ "$(echo "$OUT" | tail -1)" = "0" ]
check $? "a second request reuses the connection" "$OUT"

# A body sent with `Expect: 100-continue`, as git does for a large push: the
# origin's interim response must not be taken for the answer.
head -c 200000 /dev/zero | tr '\0' 'x' > "$WORK/big"
OUT="$(curl -s --proxy "http://kleis:$TLS_ECHO_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic --cacert "$CA" -H "Expect: 100-continue" -H "Content-Type: application/octet-stream" \
  --data-binary @"$WORK/big" \
  -w '\n%{http_code}' "https://127.0.0.1:$TLS_PORT/echo" 2>&1)"
[ "$(echo "$OUT" | tail -1)" = "200" ] && echo "$OUT" | grep -q '"method": "POST"'
check $? "a request sent with Expect: 100-continue gets its real response" "$(echo "$OUT" | tail -c 300)"

echo
echo "== issuers and passthrough"
cat > "$KLEIS_HOME/config/grants/maker.toml" <<'EOF2'
name         = "maker"
service      = "demo"
credential   = "demo/token"
max_lifetime = "1h"

datalog = '''
allowed("make") <- operation("make");
allowed("get") <- operation("get_thing"), thing($n), made($n);
check if allowed($x);
allow if grant("maker");
'''
EOF2
cat > "$KLEIS_HOME/config/config.toml" <<EOF2
listen = "127.0.0.1:$TLS_KLEIS_PORT"
mode = "connect"
upstream_ca_file = "$WORK/origin.crt"
passthrough = ["localhost"]
# The test origin is on the loopback and an arbitrary port, which passthrough
# refuses unless told otherwise.
passthrough_ports = [$ORIGIN_PORT]
passthrough_internal = true

[[issuer]]
name = "ci"
grants = ["echo-*"]
facts = ["job_*"]
max_ttl = "2h"
EOF2
kill "$KLEISD_PID" 2>/dev/null; wait "$KLEISD_PID" 2>/dev/null
"$KLEISD" > "$WORK/kleisd-issuer.log" 2>&1 &
KLEISD_PID=$!
for _ in $(seq 50); do
  curl -s -o /dev/null "http://127.0.0.1:$TLS_KLEIS_PORT/" && break
  sleep 0.1
done
ADMIN="http://127.0.0.1:$TLS_KLEIS_PORT/.kleis/v1"

ISSUER="$("$KLEIS" issuer token ci --ttl 1d)"
check $? "mint an issuer's credential"
OUT="$(curl -s -H "Authorization: Bearer $ISSUER" -H 'content-type: application/json' \
  -d '{"grants":["echo-only"],"bearer":"job-1","ttl":"1h","facts":[{"name":"job_id","terms":["1"]}]}' \
  "$ADMIN/tokens")"
JOB_TOKEN="$(echo "$OUT" | python3 -c 'import json,sys;print(json.load(sys.stdin)["token"])' 2>/dev/null)"
JOB_REV="$(echo "$OUT" | python3 -c 'import json,sys;print(json.load(sys.stdin)["revocation_ids"][0])' 2>/dev/null)"
[ -n "$JOB_TOKEN" ]; check $? "the issuer mints a token" "$OUT"
"$KLEIS" token inspect --token "$JOB_TOKEN" | grep -q 'issued_by("ci")'
check $? "which says who issued it" "$("$KLEIS" token inspect --token "$JOB_TOKEN")"
OUT="$(curl -s --proxy "http://kleis:$JOB_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic --cacert "$CA" "https://127.0.0.1:$TLS_PORT/echo" 2>&1)"
echo "$OUT" | grep -q '"authorization": "Bearer upstream-secret-42"'
check $? "and the token spends its grant" "$OUT"

CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Authorization: Bearer $ISSUER" \
  -H 'content-type: application/json' -d '{"grants":["dev-only"]}' "$ADMIN/tokens")"
[ "$CODE" = "403" ]; check $? "an issuer cannot name a grant outside its list" "got $CODE: $(cat "$WORK/body")"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Authorization: Bearer $ISSUER" \
  -H 'content-type: application/json' \
  -d '{"grants":["echo-only"],"facts":[{"name":"operation","terms":["echo"]}]}' "$ADMIN/tokens")"
[ "$CODE" = "403" ]; check $? "nor state a fact the proxy gives meaning to" "got $CODE: $(cat "$WORK/body")"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Authorization: Bearer $ISSUER" \
  -H 'content-type: application/json' -d '{"grants":["echo-only"],"ttl":"3h"}' "$ADMIN/tokens")"
[ "$CODE" = "403" ]; check $? "nor outlive its maximum" "got $CODE: $(cat "$WORK/body")"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Authorization: Bearer $JOB_TOKEN" \
  -H 'content-type: application/json' -d '{"grants":["echo-only"]}' "$ADMIN/tokens")"
[ "$CODE" = "403" ]; check $? "and a bearer's token is not an issuer's" "got $CODE"

CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Authorization: Bearer $ISSUER" \
  -H 'content-type: application/json' -d "{\"revocation_id\":\"$JOB_REV\"}" "$ADMIN/revoke")"
[ "$CODE" = "200" ]; check $? "the issuer revokes what it issued" "got $CODE: $(cat "$WORK/body")"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' \
  --proxy "http://kleis:$JOB_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" --proxy-basic --cacert "$CA" \
  "https://127.0.0.1:$TLS_PORT/echo")"
[ "$CODE" = "403" ] && grep -q revoked "$WORK/body"
check $? "and the token stops working at once" "got $CODE: $(cat "$WORK/body")"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Authorization: Bearer $ISSUER" \
  -H 'content-type: application/json' \
  -d "{\"revocation_id\":\"$("$KLEIS" token inspect --token "$TLS_TOKEN" | sed -n '/revocation ids:/{n;p}' | tr -d ' ')\"}" \
  "$ADMIN/revoke")"
[ "$CODE" = "403" ]; check $? "but not what somebody else issued" "got $CODE: $(cat "$WORK/body")"

# A revocation made at the command line reaches the running daemon too.
ECHO_REV="$("$KLEIS" token inspect --token "$TLS_ECHO_TOKEN" | sed -n '/revocation ids:/{n;p}' | tr -d ' ')"
"$KLEIS" token revoke "$ECHO_REV" > /dev/null
sleep 4
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' \
  --proxy "http://kleis:$TLS_ECHO_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" --proxy-basic --cacert "$CA" \
  "https://127.0.0.1:$TLS_PORT/echo")"
[ "$CODE" = "403" ] && grep -q revoked "$WORK/body"
check $? "a revocation at the command line reaches the running daemon" "got $CODE: $(cat "$WORK/body")"

PASS_TOKEN="$("$KLEIS" token issue --grant echo-only --bearer ci@pass --ttl 1h)"
# `localhost` is no manifest's, and the configuration lets it through: a blind
# tunnel, with nothing injected.
OUT="$(curl -s --proxytunnel --proxy "http://kleis:$PASS_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic "http://localhost:$ORIGIN_PORT/echo" 2>&1)"
echo "$OUT" | grep -q '"path": "/echo"' && ! echo "$OUT" | grep -q 'upstream-secret-42'
check $? "a passthrough host is tunnelled without a credential" "$OUT"
OUT="$(curl -s --proxy "http://kleis:$PASS_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic "http://localhost:$ORIGIN_PORT/echo" 2>&1)"
echo "$OUT" | grep -q '"path": "/echo"' && ! echo "$OUT" | grep -qi 'proxy-authorization'
check $? "and forwarded without the proxy's header" "$OUT"
CODE="$(curl -s -o /dev/null -w '%{http_code}' --proxytunnel \
  --proxy "http://kleis:$JOB_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" --proxy-basic \
  "http://localhost:$ORIGIN_PORT/echo" 2>&1)"
[ "$CODE" != "200" ]; check $? "but not for a revoked token" "got $CODE"
CODE="$(curl -s -o /dev/null -w '%{http_code}' --proxytunnel \
  --proxy "http://kleis:$PASS_TOKEN@127.0.0.1:$TLS_KLEIS_PORT" --proxy-basic \
  "http://127.0.0.2:$ORIGIN_PORT/echo" 2>&1)"
[ "$CODE" != "200" ]; check $? "and not for a host the configuration does not name" "got $CODE"

echo
echo "== what a token made, it may use"
MAKER_TOKEN="$("$KLEIS" token issue --grant maker --bearer ci@maker --ttl 1h)"
MP="http://kleis:$MAKER_TOKEN@127.0.0.1:$TLS_KLEIS_PORT"
CODE="$(curl -s -o /dev/null -w '%{http_code}' --proxy "$MP" --proxy-basic --cacert "$CA" \
  "https://127.0.0.1:$TLS_PORT/echo/thing/widget")"
[ "$CODE" = "403" ]; check $? "a thing the token has not made is refused" "got $CODE"
CODE="$(curl -s -o /dev/null -w '%{http_code}' --proxy "$MP" --proxy-basic --cacert "$CA" \
  -X POST "https://127.0.0.1:$TLS_PORT/echo/make/widget")"
[ "$CODE" = "200" ]; check $? "making it succeeds" "got $CODE"
CODE="$(curl -s -o /dev/null -w '%{http_code}' --proxy "$MP" --proxy-basic --cacert "$CA" \
  "https://127.0.0.1:$TLS_PORT/echo/thing/widget")"
[ "$CODE" = "200" ]; check $? "and then the token that made it may use it" "got $CODE"
OTHER_MAKER="$("$KLEIS" token issue --grant maker --bearer ci@other --ttl 1h)"
CODE="$(curl -s -o /dev/null -w '%{http_code}' --proxy "http://kleis:$OTHER_MAKER@127.0.0.1:$TLS_KLEIS_PORT" \
  --proxy-basic --cacert "$CA" "https://127.0.0.1:$TLS_PORT/echo/thing/widget")"
[ "$CODE" = "403" ]; check $? "while another token may not" "got $CODE"

echo
echo "== a daemon configured from files, as a NixOS module runs it"
DECL="$WORK/declared"
DECL_PORT="$(free_port)"
mkdir -p "$DECL/home/config/services" "$DECL/home/config/grants" "$DECL/home/config/credentials" "$DECL/secrets" "$DECL/issuers"
head -c 32 /dev/urandom | od -An -tx1 | tr -d ' \n' > "$DECL/secrets/root_key"
printf 'file-secret-77' > "$DECL/secrets/demo_token"
cp "$KLEIS_HOME/config/services/demo.toml" "$DECL/home/config/services/"
cp "$KLEIS_HOME/config/grants/echo.toml" "$DECL/home/config/grants/"
sed -i 's|credential   = "demo/token"|credential   = "demo/from-file"|' "$DECL/home/config/grants/echo.toml"
cat > "$DECL/home/config/credentials/demo.toml" <<EOF2
name        = "demo/from-file"
service     = "demo"
secret_file = "$DECL/secrets/demo_token"
EOF2
cat > "$DECL/home/config/config.toml" <<EOF2
listen = "127.0.0.1:$DECL_PORT"
mode = "rewrite"
passthrough = ["localhost"]

[[issuer]]
name = "ci"
grants = ["echo-*"]
facts = ["job_*"]
max_ttl = "2h"
token_file = "$DECL/issuers/ci.token"
EOF2
(
  export KLEIS_HOME="$DECL/home" KLEIS_ROOT_KEY_FILE="$DECL/secrets/root_key"
  unset KLEIS_STORE_KEY
  CHECK_OUT="$("$KLEISD" --check 2>&1)"
  echo "$CHECK_OUT" | grep -q "credential demo/from-file ← $DECL/secrets/demo_token$"
  check $? "the declared credential is found, and its file"
  "$KLEISD" > "$DECL/kleisd.log" 2>&1 &
  DECL_PID=$!
  for _ in $(seq 50); do
    curl -s -o /dev/null "http://127.0.0.1:$DECL_PORT/" && break
    sleep 0.1
  done
  [ -s "$DECL/issuers/ci.token" ]; check $? "the issuer's credential is written to its file"
  MODE="$(stat -c %a "$DECL/issuers/ci.token")"
  [ "$MODE" = "640" ]; check $? "readable by its group and nobody else" "mode $MODE"
  FIRST="$(cat "$DECL/issuers/ci.token")"
  OUT="$(curl -s -H "Authorization: Bearer $FIRST" -H 'content-type: application/json' \
    -d '{"grants":["echo-only"],"ttl":"1h"}' "http://127.0.0.1:$DECL_PORT/.kleis/v1/tokens")"
  JOB="$(echo "$OUT" | python3 -c 'import json,sys;print(json.load(sys.stdin)["token"])' 2>/dev/null)"
  [ -n "$JOB" ]; check $? "and it mints tokens" "$OUT"
  OUT="$(curl -s -H "Proxy-Authorization: Bearer $JOB" \
    "http://127.0.0.1:$DECL_PORT/http/127.0.0.1:$ORIGIN_PORT/echo")"
  echo "$OUT" | grep -q '"authorization": "Bearer file-secret-77"'
  check $? "a request spends the credential read from its file" "$OUT"
  printf 'file-secret-88' > "$DECL/secrets/demo_token"
  OUT="$(curl -s -H "Proxy-Authorization: Bearer $JOB" \
    "http://127.0.0.1:$DECL_PORT/http/127.0.0.1:$ORIGIN_PORT/echo")"
  echo "$OUT" | grep -q '"authorization": "Bearer file-secret-88"'
  check $? "and a rotated file is used without a restart" "$OUT"
  ! grep -rq 'file-secret' "$DECL/home/data" 2>/dev/null
  check $? "the secret is never copied into kleis's own files"
  # Passthrough is confined to public addresses and port 443 unless told otherwise.
  CODE="$(curl -s -o "$DECL/pt" -w '%{http_code}' --proxy "http://kleis:$JOB@127.0.0.1:$DECL_PORT" \
    --proxy-basic "http://localhost:443/")"
  [ "$CODE" != "200" ] && grep -q "does not tunnel to\|could not be reached" "$DECL/pt"
  check $? "passthrough does not reach the loopback by default" "got $CODE: $(cat "$DECL/pt")"
  CODE="$(curl -s -o "$DECL/pt" -w '%{http_code}' --proxy "http://kleis:$JOB@127.0.0.1:$DECL_PORT" \
    --proxy-basic "http://localhost:$ORIGIN_PORT/echo")"
  [ "$CODE" = "403" ]; check $? "nor a port it was not given" "got $CODE: $(cat "$DECL/pt")"
  # A request smuggled behind a body: the bytes after it are not relayed, and the
  # connection is closed rather than left with an answer nobody asked for.
  python3 - "$DECL_PORT" "$ORIGIN_PORT" "$JOB" > "$DECL/smuggle" <<'PY'
import socket, sys
port, origin, token = int(sys.argv[1]), sys.argv[2], sys.argv[3]
s = socket.create_connection(("127.0.0.1", port))
smuggled = f"GET /echo/SMUGGLED HTTP/1.1\r\nHost: 127.0.0.1:{origin}\r\n\r\n"
s.sendall((f"POST /http/127.0.0.1:{origin}/echo HTTP/1.1\r\nHost: 127.0.0.1\r\n"
           f"Proxy-Authorization: Bearer {token}\r\nContent-Length: 2\r\n\r\nhi" + smuggled).encode())
s.settimeout(5)
data = b""
try:
    while True:
        chunk = s.recv(65536)
        if not chunk: break
        data += chunk
except socket.timeout:
    pass
print(data.decode("latin1"))
PY
  [ "$(grep -c '^HTTP/1.1 ' "$DECL/smuggle")" = "1" ] && ! grep -q SMUGGLED "$DECL/smuggle"
  check $? "bytes behind a body are not relayed as a request" "$(head -c 400 "$DECL/smuggle")"
  # The next request — another connection, which may be given the pooled one to the
  # origin — gets its own answer, not one the smuggled request left there.
  OUT="$(curl -s -H "Proxy-Authorization: Bearer $JOB" \
    "http://127.0.0.1:$DECL_PORT/http/127.0.0.1:$ORIGIN_PORT/echo?n=second")"
  echo "$OUT" | grep -q '"path": "/echo?n=second"' && ! echo "$OUT" | grep -q SMUGGLED
  check $? "and the next request gets its own answer" "$OUT"
  CODE="$(curl -s -o /dev/null -w '%{http_code}' -H "Proxy-Authorization: Bearer $JOB" \
    "http://127.0.0.1:$DECL_PORT/http/127.0.0.1:$ORIGIN_PORT/echo%0d%0aX-Injected:%20yes")"
  [ "$CODE" = "400" ]; check $? "a CR LF in the path is refused" "got $CODE"
  CODE="$(curl -s --path-as-is -o /dev/null -w '%{http_code}' -H "Proxy-Authorization: Bearer $JOB" \
    "http://127.0.0.1:$DECL_PORT/http/127.0.0.1:$ORIGIN_PORT/echo/../x")"
  [ "$CODE" = "400" ]; check $? "and so is a dot segment" "got $CODE"
  kill "$DECL_PID" 2>/dev/null; wait "$DECL_PID" 2>/dev/null
  "$KLEISD" > "$DECL/kleisd2.log" 2>&1 &
  DECL_PID=$!
  for _ in $(seq 50); do
    curl -s -o /dev/null "http://127.0.0.1:$DECL_PORT/" && break
    sleep 0.1
  done
  [ "$(cat "$DECL/issuers/ci.token")" = "$FIRST" ]
  check $? "a restart keeps a credential that is still good"
  rm -rf "$DECL/home/data"
  kill "$DECL_PID" 2>/dev/null; wait "$DECL_PID" 2>/dev/null
  "$KLEISD" > "$DECL/kleisd3.log" 2>&1 &
  DECL_PID=$!
  for _ in $(seq 50); do
    curl -s -o /dev/null "http://127.0.0.1:$DECL_PORT/" && break
    sleep 0.1
  done
  CODE="$(curl -s -o /dev/null -w '%{http_code}' -H "Proxy-Authorization: Bearer $JOB" \
    "http://127.0.0.1:$DECL_PORT/http/127.0.0.1:$ORIGIN_PORT/echo")"
  [ "$CODE" = "200" ]; check $? "with the root key in a file, a token outlives the data directory" "got $CODE"
  kill "$DECL_PID" 2>/dev/null; wait "$DECL_PID" 2>/dev/null
  # The subshell's counts do not reach the parent; report through a file.
  echo "$PASS $FAIL" > "$DECL/counts"
)
read -r SUB_PASS SUB_FAIL < "$DECL/counts" 2>/dev/null || { SUB_PASS=0; SUB_FAIL=1; }
PASS=$SUB_PASS; FAIL=$SUB_FAIL
echo
echo "== the audit log"
"$KLEIS" audit verify | grep -q 'chain intact'
check $? "the audit chain is intact" "$("$KLEIS" audit verify)"
LINES="$(wc -l < "$KLEIS_HOME/data/audit.log")"
[ "$LINES" -ge 6 ]; check $? "every decision was recorded" "got $LINES lines"
grep -q 'upstream-secret-42' "$KLEIS_HOME/data/audit.log"
if [ $? -eq 0 ]; then bad "the log never contains the secret"; else ok "the log never contains the secret"; fi

echo
if [ "$FAIL" -eq 0 ]; then
  echo "$PASS checks passed"
  exit 0
else
  echo "$PASS passed, $FAIL FAILED"
  echo "--- kleisd log ---"; tail -30 "$WORK/kleisd.log"
  exit 1
fi
