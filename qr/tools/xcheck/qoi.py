#!/usr/bin/env python3
"""QOI against Pillow: pictures Lean encodes decode in Pillow to the same
RGBA, and pictures Pillow encodes decode in Lean to the same RGBA.

usage: qoi.py QR_TOOL WORKDIR
"""
import os
import random
import subprocess
import sys

from PIL import Image

tool, work = sys.argv[1], sys.argv[2]
os.makedirs(work, exist_ok=True)
rng = random.Random(7)


def pictures():
    yield 'one', Image.new('RGBA', (1, 1), (1, 2, 3, 4))
    yield 'flat-run', Image.new('RGBA', (300, 7), (0, 0, 0, 255))
    g = Image.new('RGBA', (256, 64))
    g.putdata([(x, (x * 3 + y) % 256, (255 - x + y) % 256, 255) for y in range(64) for x in range(256)])
    yield 'gradient', g
    n = Image.new('RGBA', (97, 61))
    n.putdata([tuple(rng.randrange(256) for _ in range(4)) for _ in range(97 * 61)])
    yield 'noise-alpha', n
    p = Image.new('RGBA', (120, 80))
    pal = [tuple(rng.randrange(256) for _ in range(3)) + (255,) for _ in range(9)]
    p.putdata([pal[rng.randrange(9)] for _ in range(120 * 80)])
    yield 'palette', p
    s = Image.new('RGBA', (2048, 3))
    s.putdata([((x // 7) % 256, (x // 3) % 256, x % 256, 255 if x % 50 else 128) for _ in range(3) for x in range(2048)])
    yield 'wide', s
    photo = Image.radial_gradient('L').resize((640, 480)).convert('RGBA')
    yield 'radial', photo


bad = 0
total = 0
for name, im in pictures():
    raw = f'{work}/{name}.rgba'
    open(raw, 'wb').write(im.tobytes())
    # Lean encodes, Pillow decodes
    subprocess.run([tool, 'qoi-encode', raw, str(im.width), str(im.height), f'{work}/{name}.lean.qoi'], check=True)
    back = Image.open(f'{work}/{name}.lean.qoi').convert('RGBA')
    ok1 = back.size == im.size and back.tobytes() == im.tobytes()
    # Pillow encodes, Lean decodes
    im.save(f'{work}/{name}.pil.qoi')
    r = subprocess.run([tool, 'qoi-decode', f'{work}/{name}.pil.qoi', f'{work}/{name}.back'],
                       capture_output=True, text=True)
    ok2 = r.stdout.split() == [str(im.width), str(im.height)] and \
        open(f'{work}/{name}.back', 'rb').read() == im.tobytes()
    total += 2
    bad += (not ok1) + (not ok2)
    sizes = (os.path.getsize(f'{work}/{name}.lean.qoi'), os.path.getsize(f'{work}/{name}.pil.qoi'))
    print(f'{name} {im.size[0]}x{im.size[1]}: Lean->Pillow {"ok" if ok1 else "DIFFERS"}, '
          f'Pillow->Lean {"ok" if ok2 else "DIFFERS"} (bytes Lean {sizes[0]}, Pillow {sizes[1]})')
print(f'QOI vs Pillow: {total - bad} agree, {bad} differ')
sys.exit(1 if bad else 0)
