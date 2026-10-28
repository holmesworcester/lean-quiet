#!/usr/bin/env bash
# The twin demo on the headless twin (host/host.c): the seam's effects
# from a script, checked by the control replies and the dumped screens.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=${1:-$root/out/host-twin}
mkdir -p "$out"
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
(cd "$root" && "$ELAN_HOME/bin/lake" build twin_demo >/dev/null)
cat > "$out/script" <<S
ping
state
!dump $out/start.ppm
!tap list 500 2150
!frames 2
!dump $out/tapped.ppm
!tap composer 10 10
!frames 2
!text héllo 🌍
!frames 1
state
!dump $out/ime.ppm
!send
!frames 2
state
!scroll 3000
!frames 2
state
send x
!sync
S
got=$(QUIET_SCRIPT="$out/script" "$root/.lake/build/bin/twin_demo")
echo "$got"
fails=0
ok() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fails=$((fails + 1)); fi; }
line() { echo "$got" | sed -n "$1p"; }
px() { python3 - "$1" "$2" "$3" <<'PY'
import sys
f = open(sys.argv[1], 'rb'); f.readline(); w, h = map(int, f.readline().split()); f.readline()
d = f.read(); x, y = int(sys.argv[2]), int(sys.argv[3]); i = (y * w + x) * 3
print('%02x%02x%02x' % (d[i], d[i + 1], d[i + 2]))
PY
}
ok "ping" '[ "$(line 2)" = pong ]'
ok "starts pinned, 300 bands" 'line 3 | grep -q "^b=0 ime=0 bands=300 "'
ok "composer above the navigation bar" '[ "$(px $out/start.ppm 900 2300)" = 303030 ]'
ok "a list tap toggles the newest band" '[ "$(px $out/tapped.ppm 900 2150)" = f0f0f0 ]'
ok "a composer tap opens the keyboard; text in code points" 'line 4 | grep -q "ime=900 .*text=héllo 🌍 pos=\[7, 7, 7, 7\]"'
ok "the composer rides the keyboard" '[ "$(px $out/ime.ppm 900 $((2400 - 900 - 70)))" = 303030 ]'
ok "send appends a band, empties the text" 'line 5 | grep -q "bands=301 .*text= pos=\[0, 0, 0, 0\]"'
ok "scroll" 'line 6 | grep -q "^b=3000 "'
ok "a command's reply" '[ "$(line 7)" = "ok bands=302" ]'
[ $fails = 0 ] && echo "host twin demo: PASS" || { echo "host twin demo: $fails failed"; exit 1; }
