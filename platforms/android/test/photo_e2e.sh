#!/usr/bin/env bash
# Own emulator only: never clears a developer's Pixel or another suite's AVD.
set -euo pipefail
cd "$(dirname "$0")/../../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
sdk=${ANDROID_SDK:-$HOME/android-sdk}
avd=lean-quiet-photo
serial=emulator-5592
out=$PWD/out/photo/android
mkdir -p "$out" "$ANDROID_AVD_HOME"
adb=("$sdk/platform-tools/adb" -s "$serial")
if "${adb[@]}" get-state >/dev/null 2>&1; then
  echo "$serial is occupied; refusing to replace an existing emulator" >&2
  exit 1
fi
platforms/android/test/avd.sh "$avd"
python3 platforms/native/photo_fixture.py "$out/quiet-photo-fixture.jpg"
"$sdk/emulator/emulator" -avd "$avd" -port 5592 -no-window -no-audio -no-snapshot -no-boot-anim -gpu swiftshader_indirect > "$out/emulator.log" 2>&1 &
photo_emulator_pid=$!
cleanup() {
  "${adb[@]}" emu kill >/dev/null 2>&1 || true
  kill "$photo_emulator_pid" >/dev/null 2>&1 || true
  wait "$photo_emulator_pid" || true
}
trap cleanup EXIT
for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
name=$("${adb[@]}" emu avd name | head -1 | tr -d '\r')
[ "$name" = "$avd" ] || { echo "wrong AVD: $name"; exit 1; }
"${adb[@]}" shell input keyevent KEYCODE_WAKEUP
"${adb[@]}" shell wm dismiss-keyguard
"${adb[@]}" shell svc power stayon true
"${adb[@]}" shell input keyevent KEYCODE_HOME
"${adb[@]}" shell am force-stop com.holmes.leanquiet
"${adb[@]}" install -r out/quiet.apk >/dev/null
"${adb[@]}" shell pm clear com.holmes.leanquiet >/dev/null
"${adb[@]}" push "$out/quiet-photo-fixture.jpg" /sdcard/Pictures/quiet-photo-fixture.jpg >/dev/null
"${adb[@]}" shell am broadcast -a android.intent.action.MEDIA_SCANNER_SCAN_FILE -d file:///sdcard/Pictures/quiet-photo-fixture.jpg >/dev/null
"${adb[@]}" shell am start -n com.holmes.leanquiet/.LeanActivity >/dev/null
python3 platforms/android/test/photo_e2e.py "$serial" "$out"
