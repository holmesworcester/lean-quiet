#!/usr/bin/env bash
# Build/setup and run only an owned emulator, never a physical device.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ANDROID_AVD_HOME=$PWD/out/zoom/avd
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
sdk=${ANDROID_SDK:-$HOME/android-sdk}
mkdir -p out/zoom/android "$ANDROID_AVD_HOME"
adb=("$sdk/platform-tools/adb" -s emulator-5658)
if "${adb[@]}" get-state >/dev/null 2>&1; then echo 'emulator-5658 occupied' >&2; exit 1; fi
platforms/android/test/avd.sh lean-quiet-zoom
[ -f "${LEANRT:-out/leanrt}/x86_64/libInit.a" ] || mise run android:runtime
rm -f out/zoom/android/result.txt out/zoom/android/text-size-comparison.png
: > out/zoom/android/test.log
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
zoom_inputs=$(python3 tests/zoom/apk_inputs.py)
if [ -f out/zoom/quiet-zoom.apk ] && [ "$(cat out/zoom/quiet-zoom.apk.inputs 2>/dev/null || true)" = "$zoom_inputs" ]; then
  echo 'Reusing APK with identical source, asset, SDK and runtime inputs' > out/zoom/android/build.log
else
  platforms/android/twin/build_apk.sh out/zoom/quiet-zoom.apk com.holmes.leanquiet.zoom 'Quiet Zoom' Main x86_64 arm64-v8a > out/zoom/android/build.log 2>&1
  [ "$(python3 tests/zoom/apk_inputs.py)" = "$zoom_inputs" ] || { echo 'APK inputs changed during build; rerun' >&2; exit 1; }
  printf '%s\n' "$zoom_inputs" > out/zoom/quiet-zoom.apk.inputs
fi
"$sdk/emulator/emulator" -avd lean-quiet-zoom -port 5658 -no-window -no-audio -no-snapshot -no-boot-anim -gpu swiftshader_indirect > out/zoom/android/emulator.log 2>&1 &
zoom_emulator_pid=$!
cleanup() {
  "${adb[@]}" emu kill >/dev/null 2>&1 || true
  kill "$zoom_emulator_pid" >/dev/null 2>&1 || true
  wait "$zoom_emulator_pid" || true
}
trap cleanup EXIT
for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
[ "$("${adb[@]}" emu avd name | head -1 | tr -d '\r')" = lean-quiet-zoom ]
"${adb[@]}" shell input keyevent KEYCODE_WAKEUP
"${adb[@]}" shell wm dismiss-keyguard
"${adb[@]}" shell svc power stayon true
"${adb[@]}" shell settings put system font_scale 1.0
"${adb[@]}" shell am force-stop com.holmes.leanquiet.zoom
"${adb[@]}" install --no-incremental -r out/zoom/quiet-zoom.apk >/dev/null
"${adb[@]}" shell pm clear com.holmes.leanquiet.zoom >/dev/null
"${adb[@]}" shell am start -n com.holmes.leanquiet.zoom/com.holmes.leanquiet.LeanActivity >/dev/null
python3 tests/zoom/android.py > out/zoom/android/test.log 2>&1
