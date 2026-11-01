#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export PATH="$ELAN_HOME/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
export ANDROID_SDK=${ANDROID_SDK:-$HOME/android-sdk}
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
mkdir -p out/photo-lifecycle
cap=(systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0)
if [ ! -f out/leanrt/x86_64/libInit.a ]; then
  "${cap[@]}" mise run android:runtime >out/photo-lifecycle/runtime-build.log 2>&1
fi
"${cap[@]}" bash platforms/android/twin/build_apk.sh out/photo-main.apk \
  com.holmes.leanquiet 'Lean Quiet' Main x86_64 >out/photo-lifecycle/build.log 2>&1
platforms/android/test/photo_lifecycle/build.sh out/photo-lifecycle-probe.apk >out/photo-lifecycle/probe-build.log 2>&1
python3 platforms/native/photo_fixture.py out/photo-lifecycle/quiet-photo-fixture.jpg
port=${PHOTO_LIFECYCLE_PORT:-5650};serial=emulator-$port
adb=("$ANDROID_SDK/platform-tools/adb" -s "$serial")
if "${adb[@]}" get-state >/dev/null 2>&1; then
  echo "$serial is occupied; refusing to replace another emulator" >&2;exit 2
fi
avd=lean-quiet-photo-lifecycle
platforms/android/test/avd.sh "$avd"
"$ANDROID_SDK/emulator/emulator" -avd "$avd" -port "$port" -no-window -no-audio \
  -no-snapshot -no-boot-anim -gpu swiftshader_indirect >out/photo-lifecycle/emulator.log 2>&1 &
photo_emulator_pid=$!
cleanup() {
  timeout 5 "${adb[@]}" emu kill >/dev/null 2>&1 || true
  kill "$photo_emulator_pid" >/dev/null 2>&1 || true
  for _ in $(seq 50); do kill -0 "$photo_emulator_pid" >/dev/null 2>&1 || break;sleep .1;done
  kill -KILL "$photo_emulator_pid" >/dev/null 2>&1 || true
  wait "$photo_emulator_pid" || true
}
trap cleanup EXIT
for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
[ "$("${adb[@]}" emu avd name | head -1 | tr -d '\r')" = "$avd" ]
"${adb[@]}" shell wm dismiss-keyguard
"${adb[@]}" shell svc power stayon true
platforms/android/test/seed_photo.sh "$serial" out/photo-lifecycle/quiet-photo-fixture.jpg out/photo-lifecycle
python3 platforms/android/test/photo_lifecycle/negative.py --serial "$serial" --out out/photo-lifecycle
