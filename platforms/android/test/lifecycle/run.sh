#!/usr/bin/env bash
# Provisioned Linux runner: Android SDK/NDK, API36 Google APIs x86_64 image,
# KVM, JDK17+, Python3, Rust Android target, pinned Lean/libuv source trees.
set -euo pipefail
cd "$(dirname "$0")/../../../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export PATH="$ELAN_HOME/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
export ANDROID_SDK=${ANDROID_SDK:-$HOME/android-sdk}
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
mkdir -p out/lifecycle
cap=(systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0)
if [ ! -f out/leanrt/x86_64/libInit.a ]; then
  "${cap[@]}" mise run android:runtime >out/lifecycle/runtime-build.log 2>&1
fi
"${cap[@]}" bash platforms/android/twin/build_apk.sh out/lifecycle.apk \
  com.holmes.leanquiet 'Lean Quiet' platforms.headless.TwinDemo x86_64 \
  >out/lifecycle/build.log 2>&1
platforms/android/test/lifecycle/build.sh out/lifecycle-probe.apk >out/lifecycle/probe-build.log 2>&1
platforms/android/test/ime/build.sh out/testime.apk >out/lifecycle/ime-build.log 2>&1
port=${LIFECYCLE_PORT:-5646}; serial=emulator-$port
adb=("$ANDROID_SDK/platform-tools/adb" -s "$serial")
if "${adb[@]}" get-state >/dev/null 2>&1; then
  echo "$serial is occupied; refusing to replace another emulator" >&2; exit 2
fi
avd=lean-quiet-lifecycle
platforms/android/test/avd.sh "$avd"
"$ANDROID_SDK/emulator/emulator" -avd "$avd" -port "$port" -no-window -no-audio \
  -no-snapshot -no-boot-anim -gpu swiftshader_indirect >out/lifecycle/emulator.log 2>&1 &
lifecycle_emulator_pid=$!
cleanup() {
  timeout 5 "${adb[@]}" emu kill >/dev/null 2>&1 || true
  kill "$lifecycle_emulator_pid" >/dev/null 2>&1 || true
  for _ in $(seq 50); do kill -0 "$lifecycle_emulator_pid" >/dev/null 2>&1 || break; sleep .1; done
  kill -KILL "$lifecycle_emulator_pid" >/dev/null 2>&1 || true
  wait "$lifecycle_emulator_pid" || true
}
trap cleanup EXIT
for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
[ "$("${adb[@]}" emu avd name | head -1 | tr -d '\r')" = "$avd" ]
"${adb[@]}" shell wm dismiss-keyguard
"${adb[@]}" shell svc power stayon true
python3 platforms/android/test/lifecycle/negative.py --serial "$serial" --out out/lifecycle
