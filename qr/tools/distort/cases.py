#!/usr/bin/env python3
"""The camera test suite's cases, for distort.py: sweeps of one distortion
at a time and random combinations, each sized so the symbol stays inside
the frame.

usage: cases.py OUT.tsv LABEL=symbol.pgm...
"""
import math
import random
import sys


def side_of(path):
    parts = open(path, 'rb').read().split(maxsplit=4)
    return int(parts[1])


def fit(n, mod, rot, w=640, h=480, margin=0.94):
    """The largest module size <= mod at which the rotated symbol fits."""
    r = math.radians(rot)
    k = abs(math.cos(r)) + abs(math.sin(r))
    return round(min(mod, margin * min(w, h) / (n * k)), 2)


def main():
    out = sys.argv[1]
    syms = [a.split('=', 1) for a in sys.argv[2:]]
    rows = []

    def add(name, label, path, **o):
        n = side_of(path)
        o.setdefault('mod', 5)
        o['mod'] = fit(n, float(o['mod']), float(o.get('rot', 0)))
        o.setdefault('seed', len(rows) + 1)
        rows.append(f'{name}-{label}\t{path}\t' + ' '.join(f'{k}={v}' for k, v in o.items()))

    for label, path in syms:
        for rot in [0, 15, 30, 45, 60, 90, 120, 180, 210, 270, 300, 345]:
            add(f'rot{rot}', label, path, rot=rot, blur=0.5, noise=3)
        for tilt in [0.1, 0.2, 0.3]:
            for skew in [0, 45, 90, 180, 270]:
                add(f'tilt{int(tilt * 100)}s{skew}', label, path, tilt=tilt, skew=skew, rot=10, blur=0.5,
                    noise=3)
        for mod in [3, 3.5, 4, 6, 8]:
            add(f'mod{mod}', label, path, mod=mod, rot=5, blur=0.4, noise=3)
        for blur in [0.8, 1.2, 1.6]:
            add(f'blur{blur}', label, path, mod=5, rot=20, blur=blur, noise=2)
        for noise in [8, 16, 28]:
            add(f'noise{noise}', label, path, rot=-8, blur=0.6, noise=noise)
        for light in [0.4, 0.7, 0.85]:
            add(f'light{light}', label, path, rot=12, light=light, blur=0.5, noise=4)
        for contrast in [0.25, 0.4]:
            add(f'contrast{contrast}', label, path, rot=40, contrast=contrast, blur=0.5, noise=3)
        for rot in [0, 77, 200]:
            add(f'mirror{rot}', label, path, rot=rot, mirror=1, tilt=0.12, skew=60, blur=0.5, noise=3)
        # a dark square over data: side 0.2 of the symbol (4% of its area) at M,
        # up to 0.3 (9%) at Q and 0.4 (16%) at H
        occs = {'M': [0.2], 'Q': [0.2, 0.3], 'H': [0.2, 0.3, 0.4]}.get(label, [])
        if occs:
            for occ in occs:
                add(f'occlude{occ}', label, path, rot=25, occlude=occ, blur=0.5, noise=3)
        r = random.Random(label)
        for k in range(16):
            add(f'camera{k}', label, path, mod=round(r.uniform(3.5, 7), 2), rot=r.randrange(360),
                tilt=round(r.uniform(0, 0.22), 2), skew=r.randrange(360), cx=round(r.uniform(0.46, 0.54), 2),
                cy=round(r.uniform(0.46, 0.54), 2), mirror=int(r.random() < 0.15),
                blur=round(r.uniform(0.3, 1.1), 2), noise=round(r.uniform(2, 12), 1),
                light=round(r.uniform(0, 0.6), 2), contrast=round(r.uniform(0.45, 1), 2))
    open(out, 'w').write('\n'.join(rows) + '\n')
    print(len(rows))


if __name__ == '__main__':
    main()
