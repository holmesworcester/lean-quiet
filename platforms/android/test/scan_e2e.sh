#!/usr/bin/env bash
# Join with QR code, end to end on this suite's own emulator: a real invite
# (invite_link: a fresh community's invitation, its code drawn by Link.qr)
# is the poster on the wall of the emulator's virtual scene; the app opens
# Join with QR code, its camera walks to the poster (scene.py), and the
# app must land on Choose a name holding exactly that link: the camera's
# frames decoded by Lean, parsed by Invite.parse.
#
# usage: scan_e2e.sh [apk] [out]
# env: ANDROID_AVD_HOME (default /mnt/storage/holmes-avd), AVD (default lean-quiet-scan), PORT (console port, default 5590:
#      serial emulator-PORT), GRPC (default 8590), KEEP=1 to leave the
#      emulator running, PYTHON_GRPC (a python with grpc_tools).
# Only ever talks to emulator-PORT, after checking it runs AVD.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
apk=$(realpath "${1:-$root/out/quiet.apk}")
out=$(realpath -m "${2:-$root/out/scan}")
avd=${AVD:-lean-quiet-scan}
port=${PORT:-5590}
grpc=${GRPC:-8590}
serial=emulator-$port
sdk=${ANDROID_SDK:-$HOME/android-sdk}
adb=("$sdk/platform-tools/adb" -s "$serial")
py=${PYTHON_GRPC:-python3.13}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
# the AVD on the big disk (the root filesystem keeps filling)
export ANDROID_AVD_HOME=${ANDROID_AVD_HOME:-/mnt/storage/holmes-avd}
mkdir -p "$ANDROID_AVD_HOME"
mkdir -p "$out"
rm -f "$out"/logcat.txt "$out"/screen.png

"$here/avd.sh" "$avd"

# The poster: a real invite's code, whole pixels a module, centred on a
# white 1024x1024 RGBA poster (the scene shows nothing for a grayscale PNG)
(cd "$root" && "$ELAN_HOME/bin/lake" build invite_link >/dev/null && .lake/build/bin/invite_link "$out")
invite=$(cat "$out/invite")
python3 -c "
from PIL import Image
im = Image.open('$out/poster.pgm').convert('RGBA')
p = Image.new('RGBA', (1024, 1024), (255, 255, 255, 255))
p.paste(im, ((1024 - im.width) // 2, (1024 - im.height) // 2))
p.save('$out/poster.png')"

# gRPC stubs for the scene camera
stubs=$out/grpc
if [ ! -f "$stubs/emulator_controller_pb2_grpc.py" ]; then
  mkdir -p "$stubs"
  "$py" -m grpc_tools.protoc -I "$sdk/emulator/lib" --python_out="$stubs" --grpc_python_out="$stubs" \
    "$sdk/emulator/lib/emulator_controller.proto"
fi

started=
if "${adb[@]}" get-state >/dev/null 2>&1; then
  name=$("${adb[@]}" emu avd name 2>/dev/null | head -1 | tr -d '\r')
  [ "$name" = "$avd" ] || { echo "$serial runs '$name', not $avd: refusing to touch it" >&2; exit 1; }
  "${adb[@]}" emu kill >/dev/null 2>&1 || true  # its poster is an old invite
  for _ in $(seq 30); do "${adb[@]}" get-state >/dev/null 2>&1 || break; sleep 1; done
fi
"$sdk/emulator/emulator" -avd "$avd" -port "$port" -no-window -no-audio -no-snapshot -no-boot-anim \
  -gpu swiftshader_indirect -camera-back virtualscene -virtualscene-poster "wall=$out/poster.png" \
  -grpc "$grpc" > "$out/emulator.log" 2>&1 &
echo $! > "$out/emulator.pid"
started=1
echo "started $avd on $serial (pid $(cat "$out/emulator.pid"))"
stop() {
  if [ -n "$started" ] && [ -z "${KEEP:-}" ]; then
    "${adb[@]}" emu kill >/dev/null 2>&1 || true
    pid=$(cat "$out/emulator.pid")
    for _ in $(seq 30); do kill -0 "$pid" 2>/dev/null || break; sleep 1; done
    kill "$pid" 2>/dev/null || true
  fi
}
trap stop EXIT

for _ in $(seq 150); do
  [ "$("${adb[@]}" shell getprop sys.boot_completed 2>/dev/null | tr -d '\r')" = 1 ] && break
  sleep 2
done
name=$("${adb[@]}" emu avd name | head -1 | tr -d '\r')
[ "$name" = "$avd" ] || { echo "$serial is '$name', not $avd" >&2; exit 1; }
echo "booted: $serial is $avd"
# awake and unlocked: the app draws (and answers its control channel) only
# while its window is on screen
"${adb[@]}" shell input keyevent KEYCODE_WAKEUP
"${adb[@]}" shell wm dismiss-keyguard
"${adb[@]}" shell svc power stayon true

"${adb[@]}" install -r "$apk" >/dev/null
"${adb[@]}" shell pm clear com.holmes.leanquiet >/dev/null
"${adb[@]}" shell pm grant com.holmes.leanquiet android.permission.CAMERA
"${adb[@]}" logcat -c
"${adb[@]}" shell am start -n com.holmes.leanquiet/.LeanActivity >/dev/null
ctl() { timeout 60 python3 "$root/tools/ctl.py" -s "$serial" -p $((port + 2000)) -t 50 "$@"; }
for _ in $(seq 30); do ctl ping >/dev/null 2>&1 && break; sleep 1; done
ctl "open scan"
"$py" "$here/scene.py" "$grpc" "$stubs"

ok=
for _ in $(seq 60); do
  got=$(ctl invite 2>/dev/null || true)
  if [ "$got" = "$invite" ]; then ok=1; break; fi
  sleep 2
done
"${adb[@]}" exec-out screencap -p > "$out/screen.png"
"${adb[@]}" logcat -d > "$out/logcat.txt" 2>/dev/null || true
echo "$(ctl scans)"
if [ -n "$ok" ]; then
  echo "PASS: the app scanned the invite with the emulator's camera and holds exactly that link"
else
  echo "FAIL: the app holds '$got', not the poster's invite ($out/logcat.txt, $out/screen.png)"; exit 1
fi
