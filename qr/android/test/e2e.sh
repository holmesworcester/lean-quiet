#!/usr/bin/env bash
# End to end on the harness's own emulator: the invite link, encoded by
# Lean, is the poster on the wall of the emulator's virtual scene; the
# virtual camera walks up to it; the harness hands each preview frame's Y
# plane to Lean's decoder; the test passes when logcat shows Lean decoded
# the invite. Leaves logcat, a screenshot and the poster in OUT.
#
# usage: e2e.sh APK [OUT]
# env: AVD (default qr-harness-20261027, created by avd.sh if missing),
#      PORT (console port, default 5578: serial emulator-PORT), GRPC (default
#      8578), KEEP=1 to leave the emulator running.
# Only ever talks to emulator-PORT, after checking it runs AVD.
set -euo pipefail
apk=$(realpath "$1")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out=$(realpath -m "${2:-$root/out/e2e}")
avd=${AVD:-qr-harness-20261027}
port=${PORT:-5578}
grpc=${GRPC:-8578}
serial=emulator-$port
sdk=${ANDROID_SDK:-$HOME/android-sdk}
adb=("$sdk/platform-tools/adb" -s "$serial")
py=${PYTHON_GRPC:-python3.13}
mkdir -p "$out"
rm -f "$out"/logcat.txt "$out"/screen.png

"$here/avd.sh" "$avd"

# The poster: a fresh invite, drawn by Lean's encoder (a quiet zone of 4).
python3 -c "
import random, time
r = random.Random(time.time_ns())
a = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
open('$out/invite', 'w').write('quiet://join/' + ''.join(r.choice(a) for _ in range(187)))"
invite=$(cat "$out/invite")
"$root/.lake/build/bin/qr_tool" render "$out/poster.pgm" M 1 4 1 auto "$out/invite" > "$out/poster.txt"
# whole pixels a module, centred on a white 1024x1024 RGBA poster (the
# scene shows nothing for a grayscale PNG)
python3 -c "
from PIL import Image
im = Image.open('$out/poster.pgm')
k = 1024 // im.width
im = im.resize((im.width * k, im.height * k), Image.NEAREST).convert('RGBA')
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
  echo "$serial already runs $avd (its poster is whatever it was started with)"
else
  "$sdk/emulator/emulator" -avd "$avd" -port "$port" -no-window -no-audio -no-snapshot -no-boot-anim \
    -gpu swiftshader_indirect -camera-back virtualscene -virtualscene-poster "wall=$out/poster.png" \
    -grpc "$grpc" > "$out/emulator.log" 2>&1 &
  echo $! > "$out/emulator.pid"
  started=1
  echo "started $avd on $serial (pid $(cat "$out/emulator.pid"))"
fi
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

"${adb[@]}" install -r "$apk" >/dev/null
"${adb[@]}" shell pm grant com.holmes.leanqr android.permission.CAMERA
"${adb[@]}" shell am force-stop com.android.camera2 >/dev/null 2>&1 || true
"${adb[@]}" logcat -c
"${adb[@]}" shell am start -n com.holmes.leanqr/.ScanActivity >/dev/null
sleep 4
"$py" "$here/scene.py" "$grpc" "$stubs"
"${adb[@]}" exec-out screencap -p > "$out/at-poster.png"

ok=
for _ in $(seq 60); do
  "${adb[@]}" logcat -d -s LeanQR:I AndroidRuntime:E > "$out/logcat.txt" 2>/dev/null || true
  if grep -qF "$invite" "$out/logcat.txt"; then ok=1; break; fi
  sleep 2
done
sleep 2
"${adb[@]}" exec-out screencap -p > "$out/screen.png"
"${adb[@]}" logcat -d -s LeanQR:I AndroidRuntime:E > "$out/logcat.txt" 2>/dev/null || true
grep -E "camera |frames |decoded" "$out/logcat.txt" | tail -5
if [ -n "$ok" ]; then
  echo "PASS: Lean decoded the invite from the emulator's camera (screen: $out/screen.png)"
else
  echo "FAIL: no decode of the invite in logcat ($out/logcat.txt, $out/screen.png)"; exit 1
fi
