#!/bin/sh
# Who can drive the app's control channel, in the Mac's simulator of our
# own (sim.sh), as android's ctl_guard.sh asks it of the emulator:
# - a connection whose first line is not the token gets nothing (closed);
# - a wrong token gets nothing;
# - the launch's token is answered (ok, then pong);
# - from the Mac's own Wi-Fi address (not loopback) nothing listens;
# - a RELEASE=1 build does not listen at all, and its binary holds no
#   listener.
# Ends with the development build installed again.
#
#   ctl_guard_mac.sh work_dir dev_app release_app port token
set -eu
w=$1; dev=$2; rel=$3; port=$4; tok=$5
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
here=$(cd "$(dirname "$0")" && pwd)
sim=$here/../sim.sh
lan=$(ipconfig getifaddr en0 || echo 192.0.2.1)
fail=0
check() { if [ "$2" = yes ]; then echo "ok   $1"; else echo "FAIL $1 ($3)"; fail=1; fi; }
# Sends lines to host:port and prints what comes back before the app
# closes or 3 s pass; "refused" if nothing listens.
talk() {
  python3 - "$1" "$port" "$2" <<'PY'
import socket, sys
host, port, lines = sys.argv[1], int(sys.argv[2]), sys.argv[3]
try:
    s = socket.create_connection((host, port), timeout=3)
except OSError:
    print("refused"); sys.exit(0)
s.sendall(lines.replace("|", "\n").encode() + b"\n")
got = b""
try:
    while True:
        b = s.recv(4096)
        if not b: break
        got += b
except socket.timeout:
    pass
print(got.decode(errors="replace").replace("\n", "|") or "(nothing)")
PY
}
has() { case $1 in *"$2"*) echo yes ;; *) echo no ;; esac; }

"$sim" "$w" install "$dev" >/dev/null
"$sim" "$w" launch "$port" "$tok" >/dev/null
sleep 4
r=$(talk 127.0.0.1 "ping")
check "no token: nothing answered" "$( [ "$(has "$r" pong)" = no ] && echo yes || echo no )" "$r"
r=$(talk 127.0.0.1 "token 00000000000000000000000000000000|ping")
check "a wrong token: nothing answered" "$( [ "$(has "$r" pong)$(has "$r" ok)" = nono ] && echo yes || echo no )" "$r"
r=$(talk 127.0.0.1 "token $tok|ping")
check "the launch's token: answered" "$(has "$r" "ok|pong")" "$r"
r=$(talk "$lan" "token $tok|ping")
check "the Mac's Wi-Fi address ($lan): nothing listens" "$(has "$r" refused)" "$r"

"$sim" "$w" install "$rel" >/dev/null
"$sim" "$w" launch "$port" "$tok" >/dev/null
sleep 4
r=$(talk 127.0.0.1 "token $tok|ping")
check "a RELEASE=1 build: nothing listens" "$(has "$r" refused)" "$r"
if strings "$rel/LeanQuiet" | grep -q "control: listening"; then
  check "a RELEASE=1 binary holds no listener" no "its strings name one"
else
  check "a RELEASE=1 binary holds no listener" yes ""
fi
if strings "$dev/LeanQuiet" | grep -q "control: listening"; then
  check "(the development binary does)" yes ""
else
  check "(the development binary does)" no "no listener in it: the check above proves nothing"
fi

"$sim" "$w" install "$dev" >/dev/null
"$sim" "$w" launch "$port" "$tok" >/dev/null
exit $fail
