"""Paired external-input smoke/CPU measurement, including non-debuggable APKs.

Uses the same retained database on one private emulator. CPU cost is descriptive,
not a latency guarantee or a proxy for Pixel performance. Native SurfaceControl
content is not represented by Java gfxinfo frame timings; retain those raw too.
"""
import io
import json
import os
from pathlib import Path
import re
import socket
import subprocess as sp
import sys
import time
from PIL import Image, ImageChops

serial, destination, mode = sys.argv[1:]
assert serial == 'emulator-5594', 'measurement only owns the release suite AVD'
out = Path(destination)
sdk = Path(os.environ.get('ANDROID_SDK', str(Path.home() / 'android-sdk')))
adb = [str(sdk / 'platform-tools/adb'), '-s', serial]
pkg = 'com.holmes.leanquiet'


def shell(*args):
    return sp.check_output([*adb, 'shell', *args], text=True, timeout=90).strip()


def ctl(command):
    with socket.create_connection(('127.0.0.1', 7594), timeout=120) as s:
        s.sendall((command + '\n').encode())
        return s.makefile().readline().strip()


def shot(name):
    data = sp.check_output([*adb, 'exec-out', 'screencap', '-p'], timeout=30)
    (out / f'{mode}-{name}.png').write_bytes(data)
    return Image.open(io.BytesIO(data)).convert('RGB')


if mode == 'development':
    sp.run([*adb, 'forward', 'tcp:7594', 'localabstract:leanquiet'], check=True)
    try:
        assert ctl('ping') == 'pong'
        ctl('found Release comparison|Ann')
        ctl('wait')
        ctl('chaos 200')
        ctl('wait')
        ctl('channel')
        ctl('bottom')
        (out / 'fixture.txt').write_text(ctl('state'))
    finally:
        sp.run([*adb, 'forward', '--remove', 'tcp:7594'], check=True)
time.sleep(8)
pid = shell('pidof', pkg).split()[0]


def ticks():
    # /proc stat fields 14 and 15; comm may contain whitespace.
    fields = shell('cat', f'/proc/{pid}/stat').rsplit(')', 1)[1].split()
    return int(fields[11]) + int(fields[12])


before = shot('before')
width, height = before.size
shell('dumpsys', 'gfxinfo', pkg, 'reset')
shell('logcat', '-c')
start_cpu = ticks()
start = time.monotonic()
for i in range(24):
    low, high = round(height * .72), round(height * .32)
    y0, y1 = (high, low) if i % 12 < 6 else (low, high)
    shell('input', 'swipe', str(width // 2), str(y0), str(width // 2), str(y1), '150')
    if i == 5:
        scrolled = shot('older-messages')
elapsed = time.monotonic() - start
used = ticks() - start_cpu
time.sleep(1)
after = shot('after')
# Exclude status/navigation bars and composer. The transcript must respond.
crop = (0, round(height * .18), width, round(height * .78))
assert ImageChops.difference(before.crop(crop), scrolled.crop(crop)).getbbox(), 'swipes did not change transcript pixels'
assert shell('pidof', pkg).split()[0] == pid, 'native process restarted'
(out / f'{mode}-gfxinfo.txt').write_text(shell('dumpsys', 'gfxinfo', pkg, 'framestats'))
log = shell('logcat', '-d', '--pid=' + pid)
(out / f'{mode}-logcat.txt').write_text(log)
frames = [dict(zip(['lean_ms', 'copy_ms', 'copied_rows', 'present_wait_ms'], map(float, m)))
          for m in re.findall(r'twin ms/frame: lean ([\d.]+) copy ([\d.]+) \((\d+) rows\) show ([\d.]+)', log)]
hz = int(shell('getconf', 'CLK_TCK'))
result = {'mode': mode, 'wall_seconds': elapsed, 'cpu_seconds': used / hz,
          'cpu_cores_mean': used / hz / elapsed, 'swipes': 24,
          'frame_120_window_means': frames,
          'process_survived': True, 'transcript_changed': True,
          'limitations': 'One emulator pass; 120-frame averages include interval edges, not percentiles. Native rendering bypasses Java gfxinfo.'}
(out / f'{mode}.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result), flush=True)
if mode == 'development':
    # The release launch starts at the same bottom checkpoint as development.
    sp.run([*adb, 'forward', 'tcp:7594', 'localabstract:leanquiet'], check=True)
    try:
        ctl('bottom')
        time.sleep(2)
    finally:
        sp.run([*adb, 'forward', '--remove', 'tcp:7594'], check=True)
