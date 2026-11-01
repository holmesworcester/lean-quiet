#!/usr/bin/env bash
# Provisioned runner: API36 Google APIs x86_64, KVM, JDK17+, SDK/NDK,
# pinned Lean/libuv sources and Rust Android target. All outputs stay in out/.
set -euo pipefail
cd "$(dirname "$0")/../../../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export PATH="$ELAN_HOME/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
export ANDROID_SDK=${ANDROID_SDK:-$HOME/android-sdk}
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
if [ "${OWNED_INPUT_SCOPED:-0}" != 1 ]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env OWNED_INPUT_SCOPED=1 bash "$0" "$@"
fi
out=out/owned-input-android
mkdir -p "$out"
df -h / /mnt/storage >"$out/disk.txt"
# Build prerequisites even when the runtime archive can be reused. The default
# preparation compiles the exact local Lean sources; private reuse is recorded.
if [ ! -f out/leanrt/x86_64/libInit.a ]; then
  mise run android:runtime >"$out/runtime-build.log" 2>&1
fi
prepare=(python3 platforms/android/test/owned_input/prepare.py --out "$out/native")
private=()
if [ "${OWNED_INPUT_PRIVATE_REUSE_IR:-0}" = 1 ]; then
  prepare+=(--reuse-ir);private+=(--reuse-ir)
fi
"${prepare[@]}"
bash "$out/native/build_app.sh" "$out/base.apk" com.holmes.leanquiet 'Lean Quiet' Main x86_64 >"$out/build.log" 2>&1
bash platforms/android/test/owned_input/build.sh "$out/probe.apk" >"$out/probe-build.log" 2>&1
bash platforms/android/test/ime/build.sh "$out/ime.apk" >"$out/ime-build.log" 2>&1
port=${OWNED_INPUT_PORT:-5652};serial=emulator-$port
avd=${OWNED_INPUT_AVD:-lean-quiet-owned-input}
adb=("$ANDROID_SDK/platform-tools/adb" -s "$serial")
owned_emulator_pid=
if [ "${OWNED_INPUT_REUSE_AVD:-0}" = 1 ]; then
  [ "$("${adb[@]}" emu avd name | head -1 | tr -d '\r')" = "$avd" ] || exit 2
else
  if "${adb[@]}" get-state >/dev/null 2>&1; then
    echo "$serial is occupied; refusing to replace another emulator" >&2;exit 2
  fi
  bash platforms/android/test/avd.sh "$avd"
  "$ANDROID_SDK/emulator/emulator" -avd "$avd" -port "$port" -no-window -no-audio \
    -no-snapshot -no-boot-anim -gpu swiftshader_indirect >"$out/emulator.log" 2>&1 &
  owned_emulator_pid=$!
fi
cleanup() {
  if [ -n "$owned_emulator_pid" ]; then
    timeout 5 "${adb[@]}" emu kill >/dev/null 2>&1 || true
    kill "$owned_emulator_pid" >/dev/null 2>&1 || true
    for _ in $(seq 50); do kill -0 "$owned_emulator_pid" >/dev/null 2>&1 || break;sleep .1;done
    kill -KILL "$owned_emulator_pid" >/dev/null 2>&1 || true
    wait "$owned_emulator_pid" || true
  fi
}
trap cleanup EXIT
for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
[ "$("${adb[@]}" shell getprop sys.boot_completed | tr -d '\r')" = 1 ]
[ "$("${adb[@]}" emu avd name | head -1 | tr -d '\r')" = "$avd" ]
"${adb[@]}" install -r "$out/ime.apk" >"$out/ime-install.log"
"${adb[@]}" shell am wait-for-broadcast-idle --flush-broadcast-loopers
"${adb[@]}" shell ime enable com.holmes.testime/.TestIme
"${adb[@]}" shell ime set com.holmes.testime/.TestIme
"${adb[@]}" shell settings put secure show_ime_with_hard_keyboard 0
python3 platforms/android/test/owned_input/negative.py --serial "$serial" --avd "$avd" \
  --base "$out/base.apk" --probe "$out/probe.apk" --out "$out/controls" "${private[@]}"
