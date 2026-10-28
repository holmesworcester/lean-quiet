#!/usr/bin/env python3
"""The image tools end to end, on the harness's own emulator (run by
e2e.sh after the scanner's test, with the harness in front and the virtual
camera at the poster):

1. Three pictures go into the emulator's MediaStore: a 4000x3000 JPEG
   (quadrants), a 600x400 JPEG whose EXIF says "rotate 90 clockwise" (a red
   block at its stored top-left), and a 300x300 PNG with alpha.
2. The harness's Photos button opens the system Photo Picker; all three
   are selected and added. Lean must store 2048x1536, 400x600 and 300x300.
3. The Camera button opens the system camera; the shutter and Done are
   pressed. Lean must store the photo. (When it shows the poster, Lean
   decoding the invite from the stored copy is reported too.)
4. Every stored QOI blob is pulled (run-as) and checked with Pillow: sizes,
   the quadrants' colours, the EXIF block at the top-right, the PNG's alpha.

usage: pics.py SERIAL OUT QR_TOOL INVITE_FILE
"""
import os
import re
import subprocess
import sys
import time

from PIL import Image, ImageDraw

serial, out, tool, invite_file = sys.argv[1:5]
adb = ['/home/holmes/android-sdk/platform-tools/adb', '-s', serial]
os.makedirs(out, exist_ok=True)
failures = []


def sh(*a, **k):
    return subprocess.run(adb + ['shell', *a], capture_output=True, text=True, **k).stdout


def nodes():
    sh('uiautomator', 'dump', '/sdcard/ui.xml')
    x = sh('cat', '/sdcard/ui.xml')
    found = []
    for m in re.finditer(r'<node [^>]*>', x):
        n = m.group(0)
        g = lambda k: (re.search(k + r'="([^"]*)"', n) or [None, ''])[1]
        found.append(dict(text=g('text'), desc=g('content-desc'), rid=g('resource-id'),
                          b=list(map(int, re.findall(r'\d+', g('bounds'))))))
    return found


def find(pred, what, tries=20):
    for _ in range(tries):
        hit = [n for n in nodes() if pred(n)]
        if hit:
            return hit
        time.sleep(1)
    raise SystemExit(f'FAIL: no {what} on screen')


def tap(n):
    b = n['b']
    subprocess.run(adb + ['shell', 'input', 'tap', str((b[0] + b[2]) // 2), str((b[1] + b[3]) // 2)])


def added(k, timeout=60):
    for _ in range(timeout):
        lines = [l for l in subprocess.run(adb + ['logcat', '-d', '-s', 'LeanPics:I'], capture_output=True,
                                           text=True).stdout.splitlines() if 'added:' in l]
        if len(lines) >= k:
            return [l.split('added: ', 1)[1] for l in lines]
        time.sleep(1)
    raise SystemExit(f'FAIL: Lean did not report {k} pictures')


def check(ok, what):
    print(('ok   ' if ok else 'FAIL ') + what)
    if not ok:
        failures.append(what)


# 1. the pictures, alone in the MediaStore
pics = os.path.join(out, 'pics')
os.makedirs(pics, exist_ok=True)
im = Image.new('RGB', (4000, 3000))
d = ImageDraw.Draw(im)
for x, y, c in [(0, 0, (220, 40, 40)), (2000, 0, (40, 200, 60)), (0, 1500, (40, 60, 220)),
                (2000, 1500, (230, 220, 40))]:
    d.rectangle([x, y, x + 1999, y + 1499], fill=c)
im.save(f'{pics}/big.jpg', quality=92)
im = Image.new('RGB', (600, 400), (200, 200, 200))
ImageDraw.Draw(im).rectangle([0, 0, 149, 99], fill=(255, 0, 0))
ex = Image.Exif()
ex[0x0112] = 6
im.save(f'{pics}/exif6.jpg', quality=95, exif=ex.tobytes())
im = Image.new('RGBA', (300, 300), (0, 0, 0, 0))
ImageDraw.Draw(im).ellipse([20, 20, 280, 280], fill=(30, 140, 230, 200))
im.save(f'{pics}/alpha.png')
sh('rm', '-rf', '/sdcard/Pictures', '/sdcard/DCIM/Camera')
sh('mkdir', '-p', '/sdcard/Pictures')
for f in ['big.jpg', 'exif6.jpg', 'alpha.png']:
    subprocess.run(adb + ['push', f'{pics}/{f}', f'/sdcard/Pictures/{f}'], capture_output=True)
sh('content', 'call', '--uri', 'content://media', '--method', 'scan_volume', '--arg', 'external_primary')
sh('run-as', 'com.holmes.leanqr', 'rm', '-rf', 'files/attachments')
subprocess.run(adb + ['logcat', '-c'])

# the MediaStore has them...
for _ in range(30):
    rows = sh('content', 'query', '--uri', 'content://media/external/images/media', '--projection', '_display_name')
    if all(f in rows for f in ['big.jpg', 'exif6.jpg', 'alpha.png']):
        break
    time.sleep(1)

# 2. the Photo Picker. It keeps its own copy of the MediaStore and can show
# pictures pushed a moment ago only after it has synced: if they are not
# there yet, close it (Back) and open it again.
photos = []
for attempt in range(5):
    tap(find(lambda n: n['desc'] == 'pics-photos', 'Photos button')[0])
    try:
        photos = find(lambda n: n['desc'].startswith('Photo taken'), 'photos in the picker', tries=8)
        if len(photos) == 3:
            break
    except SystemExit:
        pass
    subprocess.run(adb + ['shell', 'input', 'keyevent', 'KEYCODE_BACK'])
    time.sleep(5)
check(len(photos) == 3, f'the picker shows the 3 pictures ({len(photos)})')
for p in photos:
    tap(p)
    time.sleep(0.5)
tap(find(lambda n: n['text'] in ('Done', 'Add'), 'the picker\'s Done')[0])
said = added(3)
for s in said:
    print('  Lean:', s)

# 3. the system camera
tap(find(lambda n: n['desc'] == 'pics-camera', 'Camera button')[0])
tap(find(lambda n: n['rid'].endswith('shutter_button'), 'the camera\'s shutter')[0])
tap(find(lambda n: n['rid'].endswith('done_button'), 'the camera\'s Done')[0])
said = added(4)
print('  Lean:', said[3])
time.sleep(2)
subprocess.run(adb + ['exec-out', 'screencap', '-p'], stdout=open(f'{out}/pics.png', 'wb'))

# 4. what Lean stored
stored = []
for i in range(4):
    blob = subprocess.run(adb + ['exec-out', 'run-as', 'com.holmes.leanqr', 'cat', f'files/attachments/{i}.qoi'],
                          capture_output=True).stdout
    open(f'{pics}/stored{i}.qoi', 'wb').write(blob)
    stored.append(Image.open(f'{pics}/stored{i}.qoi').convert('RGBA'))
by_size = {im.size: im for im in stored}
big = by_size.get((2048, 1536))
check(big is not None, '4000x3000 stored at 2048x1536')
if big:
    check([big.getpixel(p)[:3] for p in [(10, 10), (2037, 10), (10, 1525), (2037, 1525)]] ==
          [(220, 40, 41), (39, 200, 60), (40, 60, 219), (230, 219, 39)] or
          all(max(abs(a - b) for a, b in zip(big.getpixel(p)[:3], c)) <= 4 for p, c in
              zip([(10, 10), (2037, 10), (10, 1525), (2037, 1525)],
                  [(220, 40, 40), (40, 200, 60), (40, 60, 220), (230, 220, 40)])),
          'its quadrants keep their colours')
ex6 = by_size.get((400, 600))
check(ex6 is not None, 'EXIF-rotated 600x400 stored upright at 400x600')
if ex6:
    check(ex6.getpixel((394, 5))[0] > 240 and ex6.getpixel((5, 5))[0] < 220,
          'its red block is at the top-right (turned 90 degrees clockwise)')
al = by_size.get((300, 300))
check(al is not None, 'the PNG stored at 300x300')
if al:
    check(al.getpixel((150, 150)) == (30, 140, 230, 200) and al.getpixel((2, 2))[3] == 0,
          'its alpha kept, unpremultiplied')
photo = [im for im in stored if im.size not in ((2048, 1536), (400, 600), (300, 300))]
check(len(photo) == 1 and max(photo[0].size) <= 2048, f'the camera photo stored ({photo[0].size if photo else None})')
if photo:
    photo[0].convert('L').save(f'{pics}/photo.pgm')
    r = subprocess.run([tool, 'decode', f'{pics}/photo.pgm'], capture_output=True, text=True).stdout.split()
    want = open(invite_file, 'rb').read().hex()
    lo, hi = photo[0].convert('L').getextrema()
    check(hi - lo > 64, f'the photo is a picture, not a blank frame (levels {lo}..{hi})')
    # Where the virtual camera points when the system camera opens is the
    # emulator's business (it can be back at its starting pose), so this is
    # reported, not required.
    seen = len(r) > 2 and r[1] == 'ok' and r[2] == want
    print('info ' + ('Lean decodes the invite from the stored photo' if seen else
                     'the photo does not show the poster (the virtual camera was elsewhere)'))
crash = subprocess.run(adb + ['logcat', '-d', '-s', 'AndroidRuntime:E'], capture_output=True, text=True).stdout
check('FATAL' not in crash, 'no crash')
print('PASS: pictures' if not failures else f'FAIL: pictures ({len(failures)} checks failed)')
sys.exit(1 if failures else 0)
