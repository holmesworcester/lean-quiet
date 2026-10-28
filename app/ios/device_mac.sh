#!/bin/sh
# The app end to end on an iPhone, on the Mac: installs the .app
# (devicectl), launches it with its console and the control channel on
# every interface (LEANQUIET_CTL_ADDR=any), reads the phone's Wi-Fi address
# from the console, and drives it from the Mac over the Wi-Fi (ctl.py):
# the chaos data if the database has none, then the app must answer, hold
# the data, have rows mounted, and keep drawing frames (stats twice, 5 s
# apart). The console goes to work_dir/out/device-console.txt. At the end
# the app is launched again without the console (ending the console's
# launch ends the app), on the phone for the person holding it.
#
#   device_mac.sh work_dir app device_id port messages
set -eu
w=$1; app=$2; dev=$3; port=$4; n=$5
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
here=$(cd "$(dirname "$0")" && pwd)
out=$w/out
mkdir -p "$out"
con=$out/device-console.txt
rm -f "$con"
xcrun devicectl device install app --device "$dev" "$app" >/dev/null
xcrun devicectl device process launch --console --terminate-existing --device "$dev" \
  --environment-variables "{\"LEANQUIET_CTL_ADDR\":\"any\",\"LEANQUIET_CTL_PORT\":\"$port\"}" \
  local.leanquiet.app > "$con" 2>&1 &
cp=$!
fail() {
  echo "FAIL: $*"
  kill "$cp" 2>/dev/null || true
  exit 1
}
ip=
for _ in $(seq 60); do
  # (devicectl's console ends lines with CR LF)
  ip=$(tr -d '\r' < "$con" | sed -n 's/^control: address en0 \([0-9.]*\)$/\1/p' | head -1)
  [ -n "$ip" ] && break
  sleep 1
done
[ -n "$ip" ] || fail "no en0 address on the console ($con)"
echo "phone at $ip"
ctl() { python3 "$here/ctl.py" -H "$ip" -p "$port" -w 60 "$@"; }
st=$(ctl state) || fail "the app does not answer at $ip:$port (local network permission?)"
echo "$st"
total=$(echo "$st" | sed -n 's/.* total \([0-9]*\) .*/\1/p')
if [ "${total:-0}" -lt 100 ]; then
  ctl "chaos $n" wait
fi
st=$(ctl state)
echo "$st"
total=$(echo "$st" | sed -n 's/.* total \([0-9]*\) .*/\1/p')
mounted=$(echo "$st" | sed -n 's/.* mounted \([0-9]*\) .*/\1/p')
[ "${total:-0}" -ge 100 ] || fail "no chaos data: $st"
[ "${mounted:-0}" -gt 0 ] || fail "no rows mounted: $st"
s1=$(ctl stats); sleep 5; s2=$(ctl stats)
echo "$s1"; echo "$s2"
f1=$(echo "$s1" | sed -n 's/^frames \([0-9]*\) .*/\1/p')
f2=$(echo "$s2" | sed -n 's/^frames \([0-9]*\) .*/\1/p')
[ "${f2:-0}" -gt "${f1:-0}" ] || fail "no frames drawn in 5 s"
ctl visible | cut -c1-300
xcrun devicectl device info processes --device "$dev" 2>/dev/null | grep -q LeanQuiet.app/LeanQuiet ||
  fail "the app is not running"
kill "$cp" 2>/dev/null || true
sleep 1
xcrun devicectl device process launch --terminate-existing --device "$dev" local.leanquiet.app >/dev/null
echo PASS
