#!/usr/bin/env python3
"""Compact cmap/hmtx data for layout, without loading outlines at startup."""
import hashlib
import struct
from pathlib import Path
from fontTools.ttLib import TTFont

ROOT = Path(__file__).resolve().parents[1]

def build():
    names = [line.split()[1] for line in (ROOT/'tools/noto.sha256').read_text().splitlines()]
    names += [f'NotoSans{loc}-Common.ttf' for loc in ('SC','TC','JP','KR')]
    out = bytearray(b'QNT1' + struct.pack('>H', len(names)))
    for name in names:
        path = ROOT/'assets'/name
        f = TTFont(path)
        if 'fvar' in f or f['OS/2'].usWeightClass != 400:
            raise ValueError(f'{name}: expected static Regular')
        cmap = f.getBestCmap()
        out += struct.pack('>IHHI', path.stat().st_size, f['head'].unitsPerEm, f['maxp'].numGlyphs, len(cmap))
        for cp,g in sorted(cmap.items()):
            out += struct.pack('>IHH', cp, f.getGlyphID(g), f['hmtx'][g][0])
    (ROOT/'assets/noto-index.bin').write_bytes(out)
    print(f'noto-index.bin: {len(out)} bytes, {hashlib.sha256(out).hexdigest()}')

if __name__ == '__main__': build()
