#!/usr/bin/env python3
"""Compare flat rendered scanlines to independently transcribed CSS tracks.

Zero pixel/RGB tolerance. This is a geometry comparison, not a claim of
whole-image parity with libquiet's fonts and icons. Full shared-mobile
content pixel parity is checked by the Lean desktop suite.
"""
import json
import sys
from pathlib import Path
from PIL import Image

root = Path(__file__).resolve().parents[2]
ref = json.loads((root / 'platforms/linux/reference/measurements.json').read_text())
out = Path(sys.argv[1]) if len(sys.argv) > 1 else root / 'out/desktop'
pixels = 0
for w, l, m, r, lo, mo, ro in ref['expected_tracks']:
    for mode in ['chat', 'settings', 'threads']:
        left, middle, right = (l, m, r) if mode == 'chat' else (lo, mo, ro)
        im = Image.open(out / f'{w}-{mode}.ppm').convert('RGB')
        assert im.size == (w, 760)
        for y in [400, 450, 500]:
            for x in range(w):
                expected = (118, 71, 199) if x < left else (247, 247, 247)
                if right and x >= left + middle:
                    expected = (229, 229, 229) if x == left + middle else (255, 255, 255)
                assert im.getpixel((x, y)) == expected, (w, mode, x, y, expected, im.getpixel((x, y)))
                pixels += 1
print(f'desktop reference: 27 images, {pixels} pixels; tolerance 0px / 0 RGB')
