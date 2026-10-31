#!/usr/bin/env bash
# Invite links on Android, on a suite-owned AVD (never a phone). The URI
# the join page opens (leanquiet://join/…, from the app's own
# Invite.uri), sent the way a browser sends it (VIEW, BROWSABLE), reaches
# the app cold (not running: it starts on Choose a name holding the
# invite) and warm (running: the same task takes the second invite); a
# malformed link changes nothing. The OS resolves leanquiet://join/ to the
# app and quiet:// (classic Quiet's) to nothing of ours, in the
# development APK and, when RELEASE_APK names one, the release APK.
# Artifacts: out/android-links (logcat, replies).
set -euo pipefail
cd "$(dirname "$0")/../../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
sdk=${ANDROID_SDK:-$HOME/android-sdk}
port=5598; serial=emulator-$port; avd=lean-quiet-links; pkg=com.holmes.leanquiet
out=$PWD/out/android-links
mkdir -p "$out" "$ANDROID_AVD_HOME"
adb=("$sdk/platform-tools/adb" -s "$serial")
if "${adb[@]}" get-state >/dev/null 2>&1; then
  echo "$serial is occupied; refusing to replace another emulator" >&2
  exit 1
fi
"$ELAN_HOME/bin/lake" build linkcheck >/dev/null
mapfile -t L < <(.lake/build/bin/linkcheck --print)   # link 1, link 2, URI 1, URI 2
[ "${#L[@]}" = 4 ] && [[ ${L[2]} = leanquiet://join/* ]]
dev=$out/development.apk
platforms/android/twin/build_apk.sh "$dev" "$pkg" 'Lean Quiet' Main x86_64 > "$out/build.log" 2>&1 || { tail -30 "$out/build.log"; exit 1; }
platforms/android/test/avd.sh "$avd"
"$sdk/emulator/emulator" -avd "$avd" -port "$port" -no-window -no-audio -no-snapshot -no-boot-anim -gpu swiftshader_indirect > "$out/emulator.log" 2>&1 &
emu=$!
cleanup() {
  "${adb[@]}" logcat -d > "$out/logcat.txt" 2>/dev/null || true
  "${adb[@]}" emu kill >/dev/null 2>&1 || true
  kill "$emu" >/dev/null 2>&1 || true
  wait "$emu" || true
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

fails=0
check() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fails=$((fails + 1)); fi; }
ctl() { python3 tools/ctl.py -s "$serial" -p 7098 -t 20 "$@" 2>>"$out/ctl.err" | tr -d '\r'; }
view() { "${adb[@]}" shell am start -W -a android.intent.action.VIEW -c android.intent.category.BROWSABLE -d "'$1'" >> "$out/am.log" 2>&1; }
until_invite() { for _ in $(seq 60); do [ "$(ctl invite)" = "$1" ] && return 0; sleep 1; done; return 1; }
resolves() { "${adb[@]}" shell cmd package resolve-activity --brief -a android.intent.action.VIEW -c android.intent.category.BROWSABLE -d "'$1'" | tr -d '\r' | tail -1; }

"${adb[@]}" install -r "$dev" >/dev/null
"${adb[@]}" shell pm clear "$pkg" >/dev/null
check "leanquiet://join/ opens Lean Quiet" '[ "$(resolves "${L[2]}")" = "$pkg/$pkg.LeanActivity" ]'
check "quiet:// (classic Quiet) does not" '[ "$(resolves quiet://join/x)" != "$pkg/$pkg.LeanActivity" ]'
"${adb[@]}" shell am force-stop "$pkg"
view "${L[2]}"
check "cold: the app starts holding the invite" 'until_invite "${L[0]}"'
check "cold: on Choose a name" 'ctl input | grep -q "page .*name "'
view "${L[3]}"
check "warm: the running app takes the second invite" 'until_invite "${L[1]}"'
check "warm: one task, no second instance" '[ "$("${adb[@]}" shell dumpsys activity activities | grep -c "Task{.*$pkg")" = 1 ]'
view "leanquiet://join/not-valid"
sleep 2
check "a malformed link changes nothing" '[ "$(ctl invite)" = "${L[1]}" ]'
if [ -n "${RELEASE_APK:-}" ]; then
  "${adb[@]}" uninstall "$pkg" >/dev/null
  "${adb[@]}" install "$RELEASE_APK" >/dev/null
  check "release: leanquiet://join/ opens Lean Quiet" '[ "$(resolves "${L[2]}")" = "$pkg/$pkg.LeanActivity" ]'
  check "release: quiet:// does not" '[ "$(resolves quiet://join/x)" != "$pkg/$pkg.LeanActivity" ]'
  view "${L[2]}"
  sleep 5
  check "release: a cold link starts the app and it keeps running" '[ -n "$("${adb[@]}" shell pidof "$pkg" | tr -d "\r")" ]'
  check "release: no control channel" '! ctl ping 2>/dev/null | grep -q pong'
fi
echo "android links: $fails failed"
[ "$fails" = 0 ]
