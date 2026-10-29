"""Independent per-pixel oracle: 50ms publications and 8ms OS refreshes.
Every !vsync dumps without returning from host.c to the Lean frame loop.
"""
import os
import pathlib
import subprocess

out = pathlib.Path('out/translate')
out.mkdir(parents=True, exist_ok=True)
W, H, TOP, BOTTOM, VIEW, OVER = 1080, 2400, 128, 2217, 2089, 32
# Current dark palette; kept independent of the renderer under test.
BG = bytes.fromhex('242424')
HOLD = bytes.fromhex('2f2f2f')
# Exact holdLine at 420dpi: pad=32, px48=126, x0=158, end=W*2/3=720.
tile = [BG * W if i < 12 or i >= 36 else BG * 158 + HOLD * (720-158) + BG * (W-720) for i in range(48)]

def line(p):
    if p < 5000:
        return bytes((p % 251, (p // 251) % 251, 77)) * W
    return tile[p % 48]

def offset(t):
    return (t if t < 500 else 1000-t) * 80

count = holes = painted = tile_changes = 0
for mode in ['chat', 'pin']:
    events = sorted([(t, 'vsync') for t in range(0, 1000, 8)] + [(t, 'frame') for t in range(50, 1000, 50)])
    script = []
    for t, kind in events:
        if kind == 'frame': script.append(f'!frame {t} {offset(t)}')
        else: script.append(f'!vsync {t} {offset(t)} {out}/{mode}-{t}.ppm')
    path = out / f'{mode}.script'
    path.write_text('\n'.join(script)+'\n')
    run = subprocess.run(['.lake/build/bin/translate', mode], env={**os.environ, 'QUIET_SCRIPT': str(path)},
                         capture_output=True, text=True, check=True)
    (out / f'{mode}.log').write_text(run.stdout + run.stderr)
    records = [list(map(int, s.split()[1:])) for s in run.stdout.splitlines() if s.startswith('vsync ')]
    assert len(records) == 125
    previous = None
    for t, serial, sample, base, origin, height in records:
        assert base == (0 if mode == 'pin' else offset((t // 50) * 50)), (t, base)
        assert serial == t // 50 + 1, (t, serial)
        assert origin == TOP - OVER and height == VIEW + 2*OVER
        data = (out / f'{mode}-{t}.ppm').read_bytes().split(b'\n', 3)[3]
        delta = 0 if mode == 'pin' else sample-base
        high = base+VIEW+OVER
        visible = []
        for y in range(TOP, BOTTOM):
            r = y-origin-delta
            if 0 <= r < height:
                expected = line(high-1-r)
                painted += 1
            else:
                expected = tile[(sample+BOTTOM-1-y) % 48]
                holes += 1
            actual = data[y*W*3:(y+1)*W*3]
            assert actual == expected, (mode,t,y,r,'row differs from translated painted/tile oracle')
            assert actual != bytes(W*3), (mode,t,y,'uncovered background row')
            visible.append(actual)
        if previous and mode == 'chat':
            pt, ps, po, rows = previous
            if ps == serial:
                dy = sample-po
                # Content and the fill tile move with the same exact translation.
                for y in range(max(0, dy), min(VIEW, VIEW + dy)):
                    assert visible[y] == rows[y-dy], (t,y,'motion waited for Lean')
                tile_changes += 1
        previous = (t,serial,sample,visible)
        count += 1
print(f'translate: {count} vsync dumps, {count*VIEW} complete viewport rows, {painted} painted-buffer rows, {holes} fill rows, {tile_changes} between-frame translations; passed')
