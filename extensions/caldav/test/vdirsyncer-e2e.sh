#!/usr/bin/env bash
# vdirsyncer + khal through kleis against a real CalDAV server (Radicale), with the setup files
# kleis hands out. The test server speaks plain HTTP, so the extension copy here allows it and the
# generated URLs are rewritten from https to http.
set -uo pipefail
C=${CAL_E2E_DIR:-/tmp/kleis-caldav-e2e}
KW=$(cd "$(dirname "$0")/../../.." && pwd)
H=$C/home; HOMEDIR=$C/agent-home
J() { nix shell nixpkgs#jq -c jq "$@"; }
pass=0; fail=0
ok()  { echo "  ok    $1"; pass=$((pass+1)); }
bad() { echo "  FAIL  $1"; [ -n "${2:-}" ] && printf '        %s\n' "$(echo "$2" | tail -c 600)"; fail=$((fail+1)); }
expect() { if grep -qF -- "$3" <<<"$2"; then ok "$1"; else bad "$1" "$2"; fi; }
cleanup() { docker rm -f cal-kleis cal-dav >/dev/null 2>&1; docker network rm cal >/dev/null 2>&1; }
cleanup
docker run --rm --user 0 -v $C:/c --entrypoint rm kleis:master -rf /c/home /c/agent-home /c/radicale >/dev/null 2>&1
mkdir -p "$H/config/credentials" "$H/config/specs" "$H/config/extensions" "$H/data" "$H/issuers" "$H/secrets" "$HOMEDIR" "$C/radicale"
printf '[server]\nhosts = 0.0.0.0:5232\n[auth]\ntype = none\n[storage]\nfilesystem_folder = /data/collections\n[rights]\ntype = owner_only\n' > "$C/radicale/config"
head -c 32 /dev/urandom | od -An -tx1 | tr -d ' \n' > "$H/secrets/root"
printf 'secretary:app-password' > "$H/secrets/caldav"
cp -r "$KW/extensions/caldav" "$H/config/extensions/"
sed -i 's/^provider = "static"$/provider = "static"\nallow_plaintext = true/' "$H/config/extensions/caldav/manifest.toml"
printf 'listen = "0.0.0.0:8180"\nmode = "connect"\npassthrough = []\nextensions = ["caldav"]\n[[issuer]]\nname = "orchestra"\ngrants = ["orchestra-*"]\nspecs = ["secretary"]\nfacts = ["task_*"]\nmax_ttl = "1h"\ntoken_file = "/kleis/issuers/orchestra.token"\n' > "$H/config/config.toml"
printf 'name = "caldav/secretary@radicale"\nservice = "caldav"\nhosts = ["radicale"]\nsecret_file = "/run/kleis-secrets/caldav"\n' > "$H/config/credentials/caldav.toml"
cat > "$H/config/specs/secretary.kleis" <<'EOF'
spec secretary
  max_ttl 1h
  account caldav/secretary@radicale
    allow read
    allow write, delete where path starts_with "secretary/" and path ends_with ".ics"
EOF
chmod -R a+rX "$H" "$C/radicale"; chmod 777 "$H/data" "$H/issuers"

docker network create cal >/dev/null
docker run -d --name cal-dav --network cal --network-alias radicale -v "$C/radicale/config:/config/config:ro" \
  tomsquest/docker-radicale:latest >/dev/null
docker run -d --name cal-kleis --network cal -p 127.0.0.1:18480:8180 --user "$(id -u):$(id -g)" \
  -v "$H/config:/kleis/config:ro" -v "$H/data:/kleis/data" -v "$H/issuers:/kleis/issuers" \
  -v "$H/secrets:/run/kleis-secrets:ro" -e KLEIS_ROOT_KEY_FILE=/run/kleis-secrets/root kleis:master >/dev/null
for i in $(seq 40); do [ -s "$H/issuers/orchestra.token" ] && curl -s -o /dev/null http://127.0.0.1:18480/ && break; sleep 1; done
sleep 3
# Two calendars on the server, made directly (not through kleis): the secretary's own, and one of another user.
docker exec cal-dav sh -c 'wget -q -O- --method=MKCALENDAR --header="Content-Type: application/xml" http://localhost:5232/secretary/personal/ >/dev/null 2>&1 || true'
curl -s -X MKCALENDAR -u secretary: --data '<?xml version="1.0"?><C:mkcalendar xmlns:D="DAV:" xmlns:C="urn:ietf:params:xml:ns:caldav"><D:set><D:prop><D:displayname>Personal</D:displayname></D:prop></D:set></C:mkcalendar>' \
  --connect-to radicale:5232:127.0.0.1:1 http://radicale:5232/secretary/personal/ >/dev/null 2>&1
docker exec -i cal-dav python3 - <<'PY' 2>/dev/null
import urllib.request,base64
def mk(path,name):
    body=f'<?xml version="1.0"?><C:mkcalendar xmlns:D="DAV:" xmlns:C="urn:ietf:params:xml:ns:caldav"><D:set><D:prop><D:displayname>{name}</D:displayname></D:prop></D:set></C:mkcalendar>'.encode()
    user=path.split("/")[1]
    r=urllib.request.Request("http://localhost:5232"+path,data=body,method="MKCALENDAR",headers={"Authorization":"Basic "+base64.b64encode(f"{user}:x".encode()).decode()})
    try: urllib.request.urlopen(r)
    except Exception as e: print(e)
mk("/secretary/personal/","Personal")
mk("/other/private/","Other")
PY

ISS=$(cat "$H/issuers/orchestra.token")
T=$(curl -s -H "Authorization: Bearer $ISS" -d '{"spec": "secretary", "ttl": "30m", "bearer": "orchestra:cal"}' http://127.0.0.1:18480/.kleis/v1/derive | J -r .token)
[ -n "$T" ] && [ "$T" != null ] && ok "a task token" || bad "a task token" "$(docker logs cal-kleis 2>&1 | tail -5)"
S=$(curl -s -H "Authorization: Bearer $T" http://127.0.0.1:18480/.kleis/v1/setup)
for f in $(J -r '.files[].path' <<<"$S"); do
  mkdir -p "$HOMEDIR/$(dirname "$f")"
  J -r --arg p "$f" '.files[] | select(.path == $p) | .content' <<<"$S" > "$HOMEDIR/$f"
done
expect "setup writes vdirsyncer's default config" "$(ls -R "$HOMEDIR/.config")" "config"
expect "setup writes khal's config" "$(cat "$HOMEDIR/.config/khal/config")" "type = discover"
sed -i 's#https://radicale/#http://radicale:5232/secretary/#' "$HOMEDIR/.config/vdirsyncer/config"
P="http://orchestra:$T@127.0.0.1:18480"
TOOLS="$(nix build --no-link --print-out-paths nixpkgs#vdirsyncer | grep -v -- -man$ | grep -v -- -dist$ | head -1)/bin:$(nix build --no-link --print-out-paths nixpkgs#khal | grep -v -- -man$ | grep -v -- -dist$ | head -1)/bin"
run() { HOME="$HOMEDIR" PATH="$TOOLS:$PATH" HTTP_PROXY="$P" http_proxy="$P" HTTPS_PROXY="$P" https_proxy="$P" NO_PROXY= no_proxy= \
        "$@" 2>&1; }

echo "== vdirsyncer through kleis"
OUT=$(run sh -c 'yes | vdirsyncer discover'); expect "discover finds the calendar" "$OUT" "personal"
OUT=$(run vdirsyncer sync); expect "sync" "$OUT" "Syncing calendars/personal"
OUT=$(run vdirsyncer metasync); echo "        metasync: $(echo "$OUT" | tail -1)"
echo "== khal"
OUT=$(run khal printcalendars); expect "khal sees the calendar" "$OUT" "ersonal"
OUT=$(run khal new -a Personal 2031-03-04 10:00 11:00 "Dentist" :: "created by the e2e test")
[ -z "$(echo "$OUT" | grep -i error)" ] && ok "khal new" || bad "khal new" "$OUT"
run khal new -a Personal 2031-03-05 09:00 10:00 "Standup" >/dev/null
OUT=$(run vdirsyncer sync); expect "sync pushes it" "$OUT" "Syncing calendars/personal"
SRV=$(docker exec cal-dav sh -c 'cat /data/collections/collection-root/secretary/personal/*.ics 2>/dev/null')
expect "the event is on the server" "$SRV" "SUMMARY:Dentist"
OUT=$(run khal list 2031-03-04 2d); expect "khal list shows it" "$OUT" "Dentist"
echo "== limits"
R=$(curl -s -x "$P" -X PUT --data-binary $'BEGIN:VCALENDAR\r\nEND:VCALENDAR\r\n' http://radicale:5232/other/private/x.ics)
expect "a write in another user's calendar is refused by kleis" "$R" "kleis:"
R=$(curl -s -x "$P" -X DELETE http://radicale:5232/secretary/personal/)
expect "deleting a whole calendar is refused by kleis" "$R" "kleis:"
F=$(grep -l "SUMMARY:Standup" "$HOMEDIR/calendars/radicale/personal/"*.ics | head -1)
echo "        deleting $F"
rm -f "$F"
OUT=$(run vdirsyncer sync); echo "$OUT" | sed 's/^/        | /' | tail -6; SRV=$(docker exec cal-dav sh -c 'ls /data/collections/collection-root/secretary/personal/ 2>/dev/null')
N=$(docker exec cal-dav sh -c 'grep -l SUMMARY:Standup /data/collections/collection-root/secretary/personal/*.ics 2>/dev/null | wc -l')
[ "$N" = 0 ] && ok "deleting an event syncs" || bad "deleting an event syncs" "$SRV"
echo; echo "$pass passed, $fail failed"
cleanup
