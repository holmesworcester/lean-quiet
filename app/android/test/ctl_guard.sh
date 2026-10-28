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
root=$(cd "$here/../.." && pwd)
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
run() {  # $1: apk
  "${adb[@]}" install -r "$1" >/dev/null
  "${adb[@]}" shell am force-stop com.holmes.leanquiet
  "${adb[@]}" shell am start -n com.holmes.leanquiet/.LeanActivity >/dev/null
  sleep 6
}
check() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fail=1; fi; }
run "$root/out/quiet.apk"
shell=$("${adb[@]}" shell /data/local/tmp/lqprobe | tr -d '\r')
check "the shell (adb) is answered" '[[ "$shell" == *pong* ]]'
other=$("${adb[@]}" shell 'run-as com.holmes.leanquiet sh -c "cp /data/local/tmp/lqprobe ./lqprobe && chmod 755 ./lqprobe && ./lqprobe; rm -f ./lqprobe"' | tr -d '\r')
check "another uid is refused, unread" '[[ "$other" != *pong* ]]'
RELEASE=1 "$root/android/twin/build_apk.sh" "$out/release.apk" com.holmes.leanquiet 'Lean Quiet' Main "$abi" >/dev/null
run "$out/release.apk"
rel=$("${adb[@]}" shell /data/local/tmp/lqprobe | tr -d '\r' || true)
check "a release build does not listen" '[[ "$rel" == *"connect failed"* ]]'
run "$root/out/quiet.apk"  # leave the development build
exit $fail
