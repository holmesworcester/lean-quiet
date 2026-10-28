#!/usr/bin/env bash
# End to end on a booted emulator (the twin demo, platforms/headless/TwinDemo.lean):
# the seam's every effect through the real OS, checked by control
# commands, the twin's trace, and screenshots.
#
# - the control socket answers (adb forward to @leanquiet);
# - a composer tap opens the keyboard (the test IME, platforms/android/test/ime: a
#   docked panel, since emulators keep Gboard in its accessory mode), and
#   the composer rides its animation frame by frame (debug.lean.trace);
# - the keyboard's text, composition and selection mirror in code points;
#   its send appends a band and empties the text;
# - the list is bottom-anchored: a drag and a fling down show older bands
#   (the offset rises), scrollTo and scrollBy (during a fling) move it;
# - a list tap toggles the band under the finger; Back closes the keyboard.
#
# usage: twin_demo_e2e.sh SERIAL [artifacts-dir]   (the APKs: out/)
set -euo pipefail
serial=${1:?serial}
art=${2:-out/e2e-twin}
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
adb=(${ADB:-$HOME/android-sdk/platform-tools/adb} -s "$serial")
port=${PORT:-17073}
mkdir -p "$art"
pkg=com.holmes.leanquiet
"$root/platforms/android/test/ime/build.sh" "$root/out/testime.apk" >/dev/null
"${adb[@]}" install -r "$root/out/testime.apk" >/dev/null
"${adb[@]}" install -r "$root/out/twin-demo.apk" >/dev/null
old_ime=$("${adb[@]}" shell settings get secure default_input_method | tr -d '\r')
restore() { "${adb[@]}" shell ime set "$old_ime" >/dev/null 2>&1 || true
  "${adb[@]}" shell setprop debug.lean.trace 0 || true; }
trap restore EXIT
"${adb[@]}" shell ime enable com.holmes.testime/.TestIme >/dev/null
"${adb[@]}" shell ime set com.holmes.testime/.TestIme >/dev/null
"${adb[@]}" shell setprop debug.lean.trace 1
"${adb[@]}" shell am force-stop $pkg
"${adb[@]}" logcat -c
"${adb[@]}" shell am start -n $pkg/.LeanActivity >/dev/null
"${adb[@]}" forward tcp:$port localabstract:leanquiet >/dev/null
fails=0
ok() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fails=$((fails + 1)); fi; }
ctl() { python3 - "$port" "$1" <<'PY'
import socket, sys, time
for _ in range(50):
    try:
        s = socket.create_connection(('127.0.0.1', int(sys.argv[1])), timeout=5)
        s.sendall((sys.argv[2] + '\n').encode())
        print(s.makefile(encoding='utf-8').readline().strip())
        break
    except OSError:
        time.sleep(0.2)
PY
}
field() { ctl state | tr ' ' '\n' | sed -n "s/^$1=//p"; }
text() { ctl state | sed 's/.*text=//; s/ pos=.*//'; }
tap() { "${adb[@]}" shell input touchscreen tap "$1" "$2"; sleep 0.6; }
shot() { "${adb[@]}" exec-out screencap -p > "$art/$1.png"; }
px() { python3 -c "from PIL import Image; print('%02x%02x%02x' % Image.open('$art/$1.png').convert('RGB').getpixel(($2, $3)))"; }

for _ in $(seq 50); do [ "$(ctl ping)" = pong ] && break; sleep 0.2; done
ok "control socket answers" '[ "$(ctl ping)" = pong ]'
sleep 0.5
ok "starts pinned to the newest band" '[ "$(field b)" = 0 ]'
shot start
read -r W H <<< "$("${adb[@]}" shell wm size | sed -n 's/.*: \([0-9]*\)x\([0-9]*\).*/\1 \2/p' | tail -1)"
# The composer (140 px, #303030) sits above the navigation bar.
ok "composer above the navigation bar" '[ "$(px start 900 $((H - 63 - 70)))" = 303030 ]'
"${adb[@]}" logcat -c
tap 300 $((H - 63 - 70))
sleep 1.2
ime=$(field ime)
ok "a composer tap opens the keyboard (ime=$ime)" '[ "${ime:-0}" -gt 300 ]'
steps=$("${adb[@]}" logcat -d -s leantrace:* | awk '{for(i=1;i<=NF;i++) if($i=="shift") print $(i+1)}' | sort -un | wc -l)
ok "the composer follows the keyboard's animation ($steps distinct shifts)" '[ "$steps" -ge 6 ]'
shot ime
ok "composer rides above the keyboard" '[ "$(px ime 900 $((H - ime - 70)))" = 303030 ]'
row1=$((H - ime + ime * 41 / 100)); row2=$((H - ime + ime * 62 / 100))
# test IME keys: row 1 "hello " "wörld " "日本 " "🌍"; row 2 compose commit del send
tap $((W * 12 / 100)) $row1; tap $((W * 37 / 100)) $row1; tap $((W * 62 / 100)) $row1; tap $((W * 87 / 100)) $row1
ok "keyboard text mirrors in code points" '[ "$(text)" = "hello wörld 日本 🌍" ] && [ "$(field pos)" = "[16," ]'
tap $((W * 12 / 100)) $row2
ok "a composition is reported" 'ctl state | grep -q "pos=\[20, 20, 16, 20\]"'
tap $((W * 37 / 100)) $row2
ok "its end is reported" 'ctl state | grep -q "pos=\[20, 20, 20, 20\]"'
tap $((W * 87 / 100)) $row2
sleep 0.5
ok "send appends a band and empties the text" '[ "$(field bands)" = 301 ] && [ -z "$(text)" ]'
"${adb[@]}" shell input keyevent BACK
sleep 1.2
ok "Back closes the keyboard" '[ "$(field ime)" = 0 ]'
"${adb[@]}" shell input touchscreen swipe 500 800 500 1400 600
sleep 1.5
b1=$(field b)
ok "a drag down shows older bands (b=$b1)" '[ "$b1" -gt 300 ] && [ "$b1" -lt 1200 ]'
"${adb[@]}" shell input touchscreen swipe 500 600 500 1800 80
sleep 3
b2=$(field b)
ok "a fling down goes further (b=$b2)" '[ "$b2" -gt $((b1 + 2000)) ]'
ctl "to 5000" >/dev/null; sleep 0.3; ctl "by 250" >/dev/null; sleep 0.3
ok "scrollTo and scrollBy move the offset" '[ "$(field b)" = 5250 ]'
"${adb[@]}" shell input touchscreen swipe 500 600 500 1800 80
sleep 0.25
before=$(field b); ctl "by 1000" >/dev/null; sleep 2.5
ok "scrollBy keeps a fling going ($before → $(field b))" '[ "$(field b)" -gt $((before + 1500)) ]'
ctl "to 0" >/dev/null; sleep 0.5
tap 500 1000
shot tap
# The band under the tap (its 6 px separator may be the tapped row) turns white.
ok "a list tap toggles the band under it" '[ "$(px tap 900 1030)" = f0f0f0 ]'
ok "no crash" '! "${adb[@]}" logcat -d | grep -q "Fatal signal\|FATAL EXCEPTION"'
"${adb[@]}" logcat -d -s lean:* > "$art/logcat.txt"
echo "screenshots and log: $art"
[ $fails = 0 ] && echo "twin demo e2e: PASS" || { echo "twin demo e2e: $fails failed"; exit 1; }
