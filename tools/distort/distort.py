#!/usr/bin/env python3
"""Synthetic camera frames of a QR code, for the decoder's tests.

Takes symbols rendered by the Lean encoder (binary PGM, 1 pixel a module,
quiet zone included) and puts each into a camera-sized frame the way a
phone sees it: a perspective view (the symbol's corners moved by a
homography, which covers rotation and scale), optionally mirrored, then
blur, uneven lighting, sensor noise, low contrast and partial occlusion.
Deterministic: every case has its own seed.

usage: distort.py CASES.tsv OUTDIR
  CASES.tsv rows: name<TAB>symbol.pgm<TAB>key=value ...
  keys: w h (frame size), mod (pixels a module), rot (degrees), tilt
  (0..0.4: perspective, as the far edge's shrink), skew (degrees the tilt
  axis is turned), cx cy (centre, 0..1 of the frame), mirror (0/1), blur
  (Gaussian radius, px), noise (sigma), light (0..1: depth of a lighting
  gradient), contrast (0..1), occlude (0..0.5: side of a dark square over
  data, as a fraction of the symbol), seed
Writes OUTDIR/<name>.pgm and prints one line per case.
"""
import math
import sys

import numpy as np
from PIL import Image, ImageFilter


def read_pgm(path):
    data = open(path, 'rb').read()
    parts = data.split(maxsplit=4)
    assert parts[0] == b'P5', path
    w, h = int(parts[1]), int(parts[2])
    px = np.frombuffer(parts[4][: w * h], dtype=np.uint8).reshape(h, w)
    return px


def write_pgm(path, px):
    h, w = px.shape
    with open(path, 'wb') as f:
        f.write(b'P5\n%d %d\n255\n' % (w, h))
        f.write(px.astype(np.uint8).tobytes())


def homography(src, dst):
    """3x3 H with dst ~ H src for four point pairs."""
    a = []
    b = []
    for (u, v), (x, y) in zip(src, dst):
        a.append([u, v, 1, 0, 0, 0, -u * x, -v * x]); b.append(x)
        a.append([0, 0, 0, u, v, 1, -u * y, -v * y]); b.append(y)
    h = np.linalg.solve(np.array(a, float), np.array(b, float))
    return np.append(h, 1).reshape(3, 3)


def frame(sym, o, rng):
    W, H = int(o.get('w', 640)), int(o.get('h', 480))
    n = sym.shape[0]  # symbol side in modules, quiet zone included
    mod = float(o.get('mod', 4.0))
    side = n * mod
    rot = math.radians(float(o.get('rot', 0)))
    tilt = float(o.get('tilt', 0))
    skew = math.radians(float(o.get('skew', 0)))
    cx, cy = float(o.get('cx', 0.5)) * W, float(o.get('cy', 0.5)) * H
    # the symbol's corners, centred, tilted (one edge shrunk towards the
    # far side along the skew axis), then rotated and placed
    corners = []
    for (sx, sy) in [(-1, -1), (1, -1), (1, 1), (-1, 1)]:
        x, y = sx * side / 2, sy * side / 2
        # project onto the tilt axis: points on its far side shrink
        ax, ay = math.cos(skew), math.sin(skew)
        t = (x * ax + y * ay) / (side / 2)  # -1..1 along the axis
        k = 1 - tilt * (t + 1) / 2
        x, y = x * k, y * k
        corners.append((cx + x * math.cos(rot) - y * math.sin(rot),
                        cy + x * math.sin(rot) + y * math.cos(rot)))
    src = [(0, 0), (n, 0), (n, n), (0, n)]
    if int(o.get('mirror', 0)):
        src = [(n, 0), (0, 0), (0, n), (n, n)]
    hm = homography(src, corners)
    hi = np.linalg.inv(hm)
    # inverse map every frame pixel's centre into module space
    ys, xs = np.mgrid[0:H, 0:W].astype(float)
    xs += 0.5; ys += 0.5
    den = hi[2, 0] * xs + hi[2, 1] * ys + hi[2, 2]
    u = (hi[0, 0] * xs + hi[0, 1] * ys + hi[0, 2]) / den
    v = (hi[1, 0] * xs + hi[1, 1] * ys + hi[1, 2]) / den
    # supersample: module value at (u, v), area-averaged by 2x2 offsets
    acc = np.zeros((H, W))
    for du in (-0.25, 0.25):
        for dv in (-0.25, 0.25):
            # offsets in pixel space mapped approximately through the scale
            uu = u + du / mod
            vv = v + dv / mod
            iu = np.floor(uu).astype(int)
            iv = np.floor(vv).astype(int)
            inside = (iu >= 0) & (iu < n) & (iv >= 0) & (iv < n)
            val = np.full((H, W), 200.0)
            val[inside] = sym[iv[inside], iu[inside]].astype(float)
            acc += val
    img = acc / 4
    # the background: a mid-grey surface with some texture
    bg = ~((u >= 0) & (u < n) & (v >= 0) & (v < n))
    tex = 150 + 40 * np.sin(xs / 37.0) * np.cos(ys / 23.0) + rng.normal(0, 6, (H, W))
    img[bg] = tex[bg]
    contrast = float(o.get('contrast', 1))
    img = 128 + (img - 128) * contrast
    light = float(o.get('light', 0))
    if light:
        ang = rng.uniform(0, 2 * math.pi)
        g = (xs * math.cos(ang) + ys * math.sin(ang))
        g = (g - g.min()) / max(g.max() - g.min(), 1)
        img = img * (1 - light * g) + 10 * light
    occ = float(o.get('occlude', 0))
    if occ:
        # a dark square over the data, in module space away from the finders
        q = 4  # quiet zone
        core = n - 2 * q
        s = occ * core
        u0 = q + core * 0.5 - s / 2 + rng.uniform(-0.1, 0.1) * core
        v0 = q + core * 0.62 - s / 2
        m = (u >= u0) & (u < u0 + s) & (v >= v0) & (v < v0 + s)
        img[m] = 40
    blur = float(o.get('blur', 0))
    pil = Image.fromarray(np.clip(img, 0, 255).astype(np.uint8))
    if blur:
        pil = pil.filter(ImageFilter.GaussianBlur(blur))
    img = np.asarray(pil).astype(float)
    noise = float(o.get('noise', 0))
    if noise:
        img = img + rng.normal(0, noise, img.shape)
    return np.clip(img, 0, 255).astype(np.uint8)


def main():
    cases, outdir = sys.argv[1], sys.argv[2]
    for line in open(cases):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        name, sym, *kv = line.split('\t')
        o = dict(x.split('=', 1) for x in ' '.join(kv).split())
        rng = np.random.default_rng(int(o.get('seed', 1)))
        px = frame(read_pgm(sym), o, rng)
        write_pgm(f'{outdir}/{name}.pgm', px)
        print(name)


if __name__ == '__main__':
    main()
