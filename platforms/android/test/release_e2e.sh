#!/usr/bin/env bash
# Build both modes and exercise them on a suite-owned AVD, never a phone.
set -euo pipefail
cd "$(dirname "$0")/../../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
sdk=${ANDROID_SDK:-$HOME/android-sdk}
serial=emulator-5594
avd=lean-quiet-release
out=$PWD/out/ctl-guard
mkdir -p "$out" "$ANDROID_AVD_HOME"
adb=("$sdk/platform-tools/adb" -s "$serial")
if "${adb[@]}" get-state >/dev/null 2>&1; then
  echo "$serial is occupied; refusing to replace another emulator" >&2
  exit 1
fi
DEV_APK=$out/development.apk
export DEV_APK
RELEASE=0 platforms/android/twin/build_apk.sh "$DEV_APK" com.holmes.leanquiet 'Lean Quiet' Main x86_64
platforms/android/test/avd.sh "$avd"
"$sdk/emulator/emulator" -avd "$avd" -port 5594 -no-window -no-audio -no-snapshot -no-boot-anim -gpu swiftshader_indirect > "$out/emulator.log" 2>&1 &
release_emulator_pid=$!
cleanup() {
  "${adb[@]}" logcat -d > "$out/logcat.txt" 2>/dev/null || true
  "${adb[@]}" emu kill >/dev/null 2>&1 || true
  kill "$release_emulator_pid" >/dev/null 2>&1 || true
  wait "$release_emulator_pid" || true
}
trap cleanup EXIT
for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
[ "$("${adb[@]}" emu avd name | head -1 | tr -d '\r')" = "$avd" ]
"${adb[@]}" shell input keyevent KEYCODE_WAKEUP
"${adb[@]}" shell wm dismiss-keyguard
"${adb[@]}" shell svc power stayon true
"${adb[@]}" shell input keyevent KEYCODE_HOME
"${adb[@]}" shell am force-stop com.holmes.leanquiet
"${adb[@]}" install -r "$DEV_APK" >/dev/null
"${adb[@]}" shell pm clear com.holmes.leanquiet >/dev/null
MEASURE_RELEASE=1 platforms/android/test/ctl_guard.sh "$serial"
