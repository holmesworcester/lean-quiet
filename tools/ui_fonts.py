#!/usr/bin/env python3
"""Static 500-weight UI face from libquiet's pinned bundled Noto (OFL).

Outlines and metrics come from the same font Chromium uses. Runtime has no
variable-font interpreter and never synthesizes weight by smearing pixels.
"""
import hashlib
from pathlib import Path
import shutil
import struct
import sys
from fontTools.ttLib import TTFont

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / 'ui/fonts/noto-sans-latin.woff2'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '51ca196f49a33e79e7870ff88ebd2829a3f627a51e7d690986618f0e7ad2b52d'
static = ROOT / 'ui/fonts/NotoSans-UI-Medium.ttf'
# Ordinary builds only copy the reviewed static face; Brotli and variable-font
# instancing are needed solely to explicitly regenerate this small source asset.
if '--regenerate' in sys.argv:
    from fontTools.varLib.instancer import instantiateVariableFont
    font = TTFont(source, recalcTimestamp=False)
    instantiateVariableFont(font, {'wght': 500}, inplace=True)
    font.flavor = None
    font.recalcTimestamp = False
    font.save(static)
assert hashlib.sha256(static.read_bytes()).hexdigest() == '476b3da941d7b2fa3720f23946b5064bd4b33168c8b0ff45315a7c4805e67687'
target = ROOT / 'assets/NotoSans-UI-Medium.ttf'
index = ROOT / 'assets/noto-ui-index.bin'
stamp = ROOT / 'assets/noto-ui.sha256'
key = hashlib.sha256(Path(__file__).read_bytes() + static.read_bytes()).hexdigest()
if not (target.exists() and index.exists() and stamp.exists() and stamp.read_text() == key):
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(static, target)
    font = TTFont(target)
    assert 'fvar' not in font and font['OS/2'].usWeightClass == 500
    cmap = font.getBestCmap()
    data = bytearray(b'QNT1' + struct.pack('>H', 1))
    data += struct.pack('>IHHI', target.stat().st_size, font['head'].unitsPerEm, font['maxp'].numGlyphs, len(cmap))
    for code, glyph in sorted(cmap.items()):
        data += struct.pack('>IHH', code, font.getGlyphID(glyph), font['hmtx'][glyph][0])
    index.write_bytes(data)
    stamp.write_text(key)
    print('UI font: pinned Noto weight 500 and cmap/hmtx index')
