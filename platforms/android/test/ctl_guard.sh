#!/usr/bin/env bash
# Who can drive the app through its control channel, on SERIAL's emulator:
# - the shell (adb) gets an answer;
# - another uid (the app's own, through run-as) is refused, unread;
# - a RELEASE=1 build does not listen at all.
# The probe (ctl_probe.c) connects to the abstract socket @leanquiet and
# sends "ping".
#
# usage: ctl_guard.sh [serial]   (default emulator-5644; never the user's)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
serial=${1:-emulator-5644}
sdk=${ANDROID_SDK:-$HOME/android-sdk}
adb=("$sdk/platform-tools/adb" -s "$serial")
ndk=$(ls -d "$sdk"/ndk/* | sort -V | tail -1)
abi=$("${adb[@]}" shell getprop ro.product.cpu.abi | tr -d '\r')
tgt=$([ "$abi" = x86_64 ] && echo x86_64-linux-android30 || echo aarch64-linux-android30)
out=$root/out/ctl-guard; mkdir -p "$out"
"$ndk/toolchains/llvm/prebuilt/linux-x86_64/bin/clang" --target=$tgt -O2 -o "$out/probe" "$here/ctl_probe.c"
"${adb[@]}" push "$out/probe" /data/local/tmp/lqprobe >/dev/null
"${adb[@]}" shell chmod 755 /data/local/tmp/lqprobe
fail=0
forward_port=$("${adb[@]}" forward tcp:0 localabstract:leanquiet)
trap '"${adb[@]}" forward --remove "tcp:$forward_port" >/dev/null 2>&1 || true' EXIT
reply() {
  python3 - "$forward_port" <<'PY'
import socket, sys
try:
    with socket.create_connection(('127.0.0.1', int(sys.argv[1])), timeout=3) as s:
        s.sendall(b'ping\n')
        answer = s.makefile().readline().strip()
        print(answer or 'connect failed')
except (OSError, TimeoutError):
    print('connect failed')
PY
}
run() {  # $1: apk
  "${adb[@]}" shell input keyevent KEYCODE_HOME
  "${adb[@]}" shell am force-stop com.holmes.leanquiet
  "${adb[@]}" install -r "$1" >/dev/null
  "${adb[@]}" shell am force-stop com.holmes.leanquiet
  "${adb[@]}" shell am start -n com.holmes.leanquiet/.LeanActivity >/dev/null
  sleep 6
}
check() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fail=1; fi; }
dev_apk=${DEV_APK:-$root/out/quiet.apk}
run "$dev_apk"
dev_flags=$("${adb[@]}" shell dumpsys package com.holmes.leanquiet)
check "development APK is debuggable" '[[ "$dev_flags" == *DEBUGGABLE* ]]'
# Android 36 SELinux denies shell-domain direct connectto; the supported
# development path is adbd's forward, which still presents uid 2000.
for _ in $(seq 30); do
  shell=$(reply)
  [[ "$shell" == *pong* ]] && break
  sleep 1
done
check "the shell (adb) is answered" '[[ "$shell" == *pong* ]]'
other=$("${adb[@]}" shell 'run-as com.holmes.leanquiet sh -c "cp /data/local/tmp/lqprobe ./lqprobe && chmod 755 ./lqprobe && ./lqprobe; rm -f ./lqprobe"' | tr -d '\r' || true)
check "another uid is refused, unread" '[[ "$other" != *pong* ]]'
if [ "${MEASURE_RELEASE:-0}" = 1 ]; then
  python3 "$here/release_measure.py" "$serial" "$out" development
fi
RELEASE=1 "$root/platforms/android/twin/build_apk.sh" "$out/release.apk" com.holmes.leanquiet 'Lean Quiet' Main "$abi" >/dev/null
run "$out/release.apk"
rel_flags=$("${adb[@]}" shell dumpsys package com.holmes.leanquiet)
check "release APK is not debuggable" '[[ "$rel_flags" != *DEBUGGABLE* ]]'
check "release APK refuses run-as" '! "${adb[@]}" shell run-as com.holmes.leanquiet id > "$out/release-run-as.txt" 2>&1'
rel=$(reply)
check "a release build does not listen" '[[ "$rel" == *"connect failed"* ]]'
if [ "${MEASURE_RELEASE:-0}" = 1 ]; then
  python3 "$here/release_measure.py" "$serial" "$out" release
fi
"${adb[@]}" logcat -d > "$out/logcat.txt"
run "$dev_apk"  # leave the development build
exit $fail
