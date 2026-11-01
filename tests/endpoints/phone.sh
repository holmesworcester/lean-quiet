#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ ${LQ_ENDPOINT_SCOPE:-0} != 1 ]]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env LQ_ENDPOINT_SCOPE=1 ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp \
    PATH=/mnt/storage/elan/bin:"$PATH" bash tests/endpoints/phone.sh "$@"
fi
adb=/home/holmes/android-sdk/platform-tools/adb
# Only the designated Pixel 7. Do not send a single device command to other phones.
serial=$($adb devices -l | awk '/model:Pixel_7 / {print $1; exit}')
[[ -n "$serial" ]] || { echo 'Pixel 7 unavailable'; exit 1; }
pkg=com.holmes.leanquiet.endpoints
out=out/endpoints/phone-$(date +%s); mkdir -p "$out"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build endpoint_network >"$out/build.log" 2>&1
platforms/android/twin/build_apk.sh "$out/phone.apk" "$pkg" 'Quiet endpoint test' tests.endpoints.Phone arm64-v8a >>"$out/build.log" 2>&1
"$adb" -s "$serial" install --no-incremental -r "$out/phone.apk" >"$out/install.log"
"$adb" -s "$serial" shell am force-stop "$pkg"
"$adb" -s "$serial" shell pm clear "$pkg" >"$out/clear.log"
local_pid=''
cleanup() {
  "$adb" -s "$serial" logcat -d -s lean >"$out/phone.log" 2>&1 || true
  "$adb" -s "$serial" shell am force-stop "$pkg" || true
  if [[ -n "$local_pid" ]]; then kill "$local_pid" 2>/dev/null || true; wait "$local_pid" 2>/dev/null || true; fi
  echo "Artifacts retained: $out"
}
trap cleanup EXIT
# Advertise the actual Wi-Fi/LAN address, never a Docker bridge.
lan=$(ip -4 route get 224.0.0.251 | sed -n 's/.* src \([^ ]*\).*/\1/p')
.lake/build/bin/endpoint_network A "$out/A.db" 49301 lan "$lan:49301" 75 >"$out/desktop.log" 2>&1 & local_pid=$!
"$adb" -s "$serial" shell input keyevent KEYCODE_WAKEUP
"$adb" -s "$serial" shell wm dismiss-keyguard
"$adb" -s "$serial" shell am start -n "$pkg/com.holmes.leanquiet.LeanActivity" >"$out/start.log"
result=''
for i in $(seq 90); do
  if (( i % 10 == 0 )); then "$adb" -s "$serial" shell input keyevent KEYCODE_WAKEUP; fi
  result=$("$adb" -s "$serial" shell run-as "$pkg" cat files/endpoint-result 2>/dev/null | tr -d '\r' || true)
  # NativeActivity uses its internalDataPath as cwd (usually files/).
  if [[ -z "$result" ]]; then result=$("$adb" -s "$serial" shell run-as "$pkg" cat endpoint-result 2>/dev/null | tr -d '\r' || true); fi
  [[ -n "$result" ]] && break
  sleep 1
done
wait "$local_pid"; local_pid=''
[[ "$result" = 0 ]] || { echo "Pixel 7 did not pass (result '$result')"; exit 1; }
"$adb" -s "$serial" logcat -d -s lean >"$out/phone.log"
grep -q 'PASS A single stable session' "$out/desktop.log"
id=$(sed -n 's/.*single stable session \([^;]*\);.*/\1/p' "$out/desktop.log")
grep -q "PASS B single stable session $id;" "$out/phone.log"
echo 'PASS Pixel 7 and desktop: LAN DNS-SD to authenticated TCP and marker exchange'
