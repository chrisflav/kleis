#!/usr/bin/env bash
# End to end: a real `curl` and a real `git push` through a running daemon.
#
# Everything happens in a temporary AUTH_HOME, against a local origin, over
# plain HTTP in rewrite mode -- so the test needs no certificate installed
# anywhere and touches nothing of the invoking user's.
set -uo pipefail

# `cd` is guarded everywhere below.  Without that, a `cd` into a directory a
# failed step never created leaves the script running in the repository it was
# launched from -- where the `git config` and `git commit` further down are
# then applied to somebody's real work.  This happened.
enter() { cd "$1" || { printf 'auth-test: cannot enter %s\n' "$1" >&2; exit 1; }; }

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"
export AUTH_HOME="$WORK/home"
export AUTH_STORE_KEY="$(printf '%064d' 7)"
AUTH="$ROOT/.lake/build/bin/auth"
AUTHD="$ROOT/.lake/build/bin/authd"

PASS=0; FAIL=0
ok()   { PASS=$((PASS+1)); printf '  ok   %s\n' "$1"; }
bad()  { FAIL=$((FAIL+1)); printf '  FAIL %s\n' "$1"; [ $# -gt 1 ] && printf '       %s\n' "$2"; }
check(){ if [ "$1" = "0" ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

cleanup() {
  [ -n "${AUTHD_PID:-}" ] && kill "$AUTHD_PID" 2>/dev/null
  [ -n "${ORIGIN_PID:-}" ] && kill "$ORIGIN_PID" 2>/dev/null
  [ -n "${TLS_ORIGIN_PID:-}" ] && kill "$TLS_ORIGIN_PID" 2>/dev/null
  rm -rf "$WORK"
}
trap cleanup EXIT

free_port() { python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1]);s.close()'; }

ORIGIN_PORT="$(free_port)"
AUTH_PORT="$(free_port)"

mkdir -p "$AUTH_HOME/config/services" "$AUTH_HOME/config/grants" "$WORK/repos"

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
cat > "$AUTH_HOME/config/config.toml" <<EOF
listen = "127.0.0.1:$AUTH_PORT"
mode = "rewrite"
EOF

cat > "$AUTH_HOME/config/services/demo.toml" <<'EOF'
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
EOF

cat > "$AUTH_HOME/config/grants/dev.toml" <<'EOF'
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

cat > "$AUTH_HOME/config/grants/read.toml" <<'EOF'
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

cat > "$AUTH_HOME/config/grants/echo.toml" <<'EOF'
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
printf 'upstream-secret-42' | "$AUTH" credential add demo/token --service demo --secret - >/dev/null
check $? "install a credential"
"$AUTHD" --check >/dev/null 2>&1
check $? "the daemon loads its configuration"

DEV_TOKEN="$("$AUTH" token issue --grant dev-only --bearer ci@test --ttl 1h)"
check $? "issue a token for the push grant"
ECHO_TOKEN="$("$AUTH" token issue --grant echo-only --bearer ci@test --ttl 1h)"
check $? "issue a token for the echo grant"
READ_TOKEN="$("$AUTH" token issue --grant read-only --bearer ci@test --ttl 1h)"
check $? "issue a token for the read-only grant"

# ---------------------------------------------------------------- the daemon
"$AUTHD" > "$WORK/authd.log" 2>&1 &
AUTHD_PID=$!
for _ in $(seq 50); do
  curl -s -o /dev/null "http://127.0.0.1:$AUTH_PORT/" && break
  sleep 0.1
done

BASE="http://127.0.0.1:$AUTH_PORT/http/127.0.0.1:$ORIGIN_PORT"

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
grep -q 'refs/heads/dev/' "$AUTH_HOME/data/audit.log"
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
REV="$("$AUTH" token list | head -1 | cut -f1)"
"$AUTH" token revoke "$REV" >/dev/null
check $? "revoke a token"
CODE="$(curl -s -o "$WORK/body" -w '%{http_code}' -H "Proxy-Authorization: Bearer $DEV_TOKEN" "$BASE/echo")"
[ "$CODE" = "403" ]; check $? "a revoked token is refused" "got $CODE"

echo
echo "== interception: real https URLs through CONNECT"
# A separate origin, over TLS, with a certificate of its own.  The proxy
# verifies it the way it would verify a real one; git verifies the proxy's
# minted leaf against the local CA.
TLS_PORT="$(free_port)"
TLS_AUTH_PORT="$(free_port)"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 1 \
  -keyout "$WORK/origin.key" -out "$WORK/origin.crt" \
  -subj "/CN=127.0.0.1" -addext "subjectAltName=IP:127.0.0.1" >/dev/null 2>&1
check $? "mint a certificate for the TLS origin"

git init --quiet --bare "$WORK/repos/tls.git"
git -C "$WORK/repos/tls.git" config http.receivepack true
python3 "$ROOT/scripts/origin.py" "$TLS_PORT" "$WORK/repos" "$WORK/origin.crt" "$WORK/origin.key" &
TLS_ORIGIN_PID=$!
sleep 1

cat > "$AUTH_HOME/config/config.toml" <<EOF
listen = "127.0.0.1:$TLS_AUTH_PORT"
mode = "connect"
upstream_ca_file = "$WORK/origin.crt"
EOF

kill "$AUTHD_PID" 2>/dev/null; wait "$AUTHD_PID" 2>/dev/null
"$AUTHD" > "$WORK/authd-tls.log" 2>&1 &
AUTHD_PID=$!
for _ in $(seq 50); do
  curl -s -o /dev/null "http://127.0.0.1:$TLS_AUTH_PORT/" && break
  sleep 0.1
done

CA="$("$AUTH" ca)"
check $? "the local CA is available"
TLS_TOKEN="$("$AUTH" token issue --grant dev-only --bearer ci@tls --ttl 1h)"
TLS_ECHO_TOKEN="$("$AUTH" token issue --grant echo-only --bearer ci@tls --ttl 1h)"

# curl, with real URLs, through the intercepting proxy.
OUT="$(curl -s --proxy "http://auth:$TLS_ECHO_TOKEN@127.0.0.1:$TLS_AUTH_PORT" \
  --proxy-basic --cacert "$CA" "https://127.0.0.1:$TLS_PORT/echo" 2>&1)"
echo "$OUT" | grep -q '"authorization": "Bearer upstream-secret-42"'
check $? "an intercepted https request carries the credential" "$OUT"

# and a real git push, over https, with the URL git was given untouched.
git config --global --unset-all "url.$BASE/.insteadOf" 2>/dev/null
git config --global --unset-all http.extraHeader 2>/dev/null
git config --global http.proxy "http://auth:$TLS_TOKEN@127.0.0.1:$TLS_AUTH_PORT"
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
echo "== the audit log"
"$AUTH" audit verify | grep -q 'chain intact'
check $? "the audit chain is intact" "$("$AUTH" audit verify)"
LINES="$(wc -l < "$AUTH_HOME/data/audit.log")"
[ "$LINES" -ge 6 ]; check $? "every decision was recorded" "got $LINES lines"
grep -q 'upstream-secret-42' "$AUTH_HOME/data/audit.log"
if [ $? -eq 0 ]; then bad "the log never contains the secret"; else ok "the log never contains the secret"; fi

echo
if [ "$FAIL" -eq 0 ]; then
  echo "$PASS checks passed"
  exit 0
else
  echo "$PASS passed, $FAIL FAILED"
  echo "--- authd log ---"; tail -30 "$WORK/authd.log"
  exit 1
fi
