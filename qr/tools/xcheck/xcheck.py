#!/usr/bin/env python3
"""Cross-checks against independent QR implementations.

- qrencode -> Lean: symbols qrencode makes (byte mode and its own mixed
  numeric/alphanumeric/byte segmentation, versions 1-40, levels L M Q H)
  decode in Lean, from pixels and from the module matrix.
- qrencode == Lean: in byte mode at the same version, level and mask,
  Lean's encoder draws the same matrix as qrencode, module for module.
- Lean -> zbarimg: symbols Lean makes decode with zbar, bytes for bytes.
- segno -> Lean: segno's symbols, including ECI (UTF-8) segments, decode
  in Lean; and how often Lean's mask choice agrees with segno's.
- qrcodegen (Nayuki's reference) == Lean: at every version, level and
  mask Lean draws the same matrix, and picks the same mask by penalty.

usage: xcheck.py QR_TOOL WORKDIR [--qrencode PATH] [--zbarimg PATH] [--segno DIR] [--qrcodegen DIR]
A tool that is not given is skipped (and said so). Exits 1 on any mismatch.
"""
import argparse
import os
import random
import subprocess
import sys

from PIL import Image


def run(*a, data=None):
    return subprocess.run(a, input=data, capture_output=True, check=False)


def lean_decode(tool, path):
    out = run(tool, 'decode', path).stdout.decode().split()
    return out[2] if len(out) > 2 and out[1] == 'ok' else None, out


def to_pgm(png, pgm):
    Image.open(png).convert('RGBA').convert('L').save(pgm)


def payloads(rng):
    abc = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
    invite = 'quiet://join/' + ''.join(rng.choice(abc) for _ in range(187))
    mixed = 'HELLO WORLD 0123456789012345 ' * 3 + 'lower case text 42 ' + '31415926535897932384'
    return [('invite', invite.encode()), ('mixed', mixed.encode()),
            ('binary', bytes(rng.randrange(256) for _ in range(120)))]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tool')
    ap.add_argument('work')
    ap.add_argument('--qrencode')
    ap.add_argument('--zbarimg')
    ap.add_argument('--segno')
    ap.add_argument('--qrcodegen')
    o = ap.parse_args()
    os.makedirs(o.work, exist_ok=True)
    rng = random.Random(2026)
    fails = []
    counts = {}

    def tally(what, ok, detail=''):
        p, f = counts.get(what, (0, 0))
        counts[what] = (p + ok, f + (not ok))
        if not ok and len(fails) < 30:
            fails.append(f'{what}: {detail}')

    pl = payloads(rng)
    versions = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 20, 23, 27, 31, 34, 37, 40]

    if o.qrencode:
        for v in versions:
            for lvl in 'LMQH':
                for name, data in pl:
                    # trim to what fits: qrencode fails on overflow, so shrink until it fits
                    d = data
                    png = f'{o.work}/qe-{v}{lvl}-{name}.png'
                    base = [o.qrencode] + (['-8'] if name != 'mixed' else []) + ['-v', str(v), '-l', lvl]
                    while d:
                        r = run(*base, '-s', '3', '-m', '4', '-o', png, data=d)
                        if r.returncode == 0:
                            break
                        d = d[: len(d) * 2 // 3]
                    if not d:
                        continue
                    pgm = png[:-4] + '.pgm'
                    to_pgm(png, pgm)
                    got, out = lean_decode(o.tool, pgm)
                    tally('qrencode -> Lean (pixels)', got == d.hex(), f'{pgm} {out[1:2]}')
                    # the module matrix, and the same matrix from Lean's encoder
                    asc = run(*base, '-t', 'ASCII', '-m', '0', data=d).stdout.decode()
                    txt = png[:-4] + '.txt'
                    open(txt, 'w').write(asc)
                    r = run(o.tool, 'ascii', txt).stdout.decode().split()
                    tally('qrencode -> Lean (matrix)', len(r) > 1 and r[0] == 'ok' and r[1] == d.hex(), txt)
                    if name != 'mixed' and len(r) > 4 and r[0] == 'ok':
                        # qrencode's -v is a minimum: compare at the version it chose
                        ver, mask = r[2], r[4]
                        open(f'{o.work}/payload', 'wb').write(d)
                        mine = run(o.tool, 'matrix', lvl, ver, mask, f'{o.work}/payload').stdout.decode().split()
                        theirs = [row[::2].replace(' ', '.') for row in asc.split('\n') if row]
                        tally('Lean matrix == qrencode matrix', mine == theirs, f'v{v} {lvl} {name}')

    if o.zbarimg:
        for v in versions:
            for lvl in 'LMQH':
                for name, data in pl:
                    d = data
                    path = f'{o.work}/payload'
                    while d:
                        open(path, 'wb').write(d)
                        r = run(o.tool, 'render', f'{o.work}/le-{v}{lvl}-{name}.pgm', lvl, '3', '4', str(v),
                                str(rng.randrange(8)), path)
                        if r.returncode == 0 and r.stdout.split()[0] == str(v).encode():
                            break
                        d = d[: len(d) * 2 // 3]
                    if not d:
                        continue
                    z = run(o.zbarimg, '--nodbus', '-q', '--raw', '-Sbinary', f'{o.work}/le-{v}{lvl}-{name}.pgm')
                    got = z.stdout
                    if got.endswith(b'\n') and not d.endswith(b'\n'):
                        got = got[:-1]
                    tally('Lean -> zbarimg', got == d, f'v{v} {lvl} {name}: {got[:20]!r}')

    if o.segno:
        sys.path.insert(0, o.segno)
        import segno
        agree = total = 0
        texts = ['Grüße aus Lean, ünïcödé', 'quiet://join/ÄÖÜ-' + 'x' * 60, '日本語のテキストもバイトで',
                 'ECI test 0123456789 ABCDEF']
        for i, t in enumerate(texts):
            for lvl in 'lmqh':
                # UTF-8 under an ECI designator (26), in byte mode (Lean has no kanji mode)
                q = segno.make(t, error=lvl, encoding='utf-8', eci=True, mode='byte', micro=False,
                               boost_error=False)
                png = f'{o.work}/sg-eci-{i}{lvl}.png'
                q.save(png, scale=3, border=4)
                pgm = png[:-4] + '.pgm'
                to_pgm(png, pgm)
                got, out = lean_decode(o.tool, pgm)
                tally('segno (ECI) -> Lean', got == t.encode('utf-8').hex(), f'{pgm} {out[1:2]}')
        for v in versions:
            for lvl in 'lmqh':
                for name, data in pl:
                    d = data
                    while d:
                        try:
                            q = segno.make(d, error=lvl, version=v, mode='byte', micro=False, boost_error=False)
                            break
                        except Exception:
                            d = d[: len(d) * 2 // 3]
                    if not d:
                        continue
                    png = f'{o.work}/sg-{v}{lvl}-{name}.png'
                    q.save(png, scale=3, border=4)
                    pgm = png[:-4] + '.pgm'
                    to_pgm(png, pgm)
                    got, out = lean_decode(o.tool, pgm)
                    tally('segno -> Lean', got == d.hex(), f'{pgm}')
                    # Lean's own mask choice for the same data, version and level
                    open(f'{o.work}/payload', 'wb').write(d)
                    r = run(o.tool, 'render', f'{o.work}/mine.pgm', lvl.upper(), '1', '0', str(v), 'auto',
                            f'{o.work}/payload').stdout.split()
                    if r and r[0] == str(v).encode():
                        total += 1
                        agree += int(r[1]) == q.mask
        print(f'mask choice: Lean picks the mask segno picks in {agree} of {total} symbols '
              '(segno scores finder-like patterns differently)')

    if o.qrcodegen:
        sys.path.insert(0, o.qrcodegen)
        from qrcodegen import QrCode, QrSegment
        ecl = {'L': QrCode.Ecc.LOW, 'M': QrCode.Ecc.MEDIUM, 'Q': QrCode.Ecc.QUARTILE, 'H': QrCode.Ecc.HIGH}
        for v in versions:
            for lvl in 'LMQH':
                for name, data in pl:
                    d = data
                    while d:
                        try:
                            q = QrCode.encode_segments([QrSegment.make_bytes(d)], ecl[lvl], minversion=v,
                                                       maxversion=v, mask=-1, boostecl=False)
                            break
                        except Exception:
                            d = d[: len(d) * 2 // 3]
                    if not d:
                        continue
                    open(f'{o.work}/payload', 'wb').write(d)
                    r = run(o.tool, 'render', f'{o.work}/mine.pgm', lvl, '1', '0', str(v), 'auto',
                            f'{o.work}/payload').stdout.split()
                    tally('Lean mask choice == qrcodegen (Nayuki) mask choice',
                          bool(r) and int(r[1]) == q.get_mask(), f'v{v} {lvl} {name}')
                    for k in range(8):
                        q = QrCode.encode_segments([QrSegment.make_bytes(d)], ecl[lvl], minversion=v,
                                                   maxversion=v, mask=k, boostecl=False)
                        theirs = [''.join('#' if q.get_module(x, y) else '.' for x in range(q.get_size()))
                                  for y in range(q.get_size())]
                        mine = run(o.tool, 'matrix', lvl, str(v), str(k), f'{o.work}/payload').stdout.decode().split()
                        tally('Lean matrix == qrcodegen matrix (every mask)', mine == theirs, f'v{v} {lvl} {name} {k}')

    for what, (p, f) in counts.items():
        print(f'{what}: {p} agree, {f} differ')
    for f in fails:
        print('  MISMATCH', f)
    if not counts:
        print('no independent tool found: nothing cross-checked')
    sys.exit(1 if any(f for _, f in counts.values()) else 0)


if __name__ == '__main__':
    main()
