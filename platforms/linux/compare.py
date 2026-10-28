#!/usr/bin/env python3
"""Compare flat rendered scanlines to independently transcribed CSS tracks.

Zero pixel/RGB tolerance. This is a geometry comparison, not a claim of
whole-image parity with libquiet's fonts, icons, or light theme.
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
                expected = (118, 71, 199) if x < left else (26, 29, 33)
                if right and x >= left + middle:
                    expected = (58, 61, 65) if x == left + middle else (38, 41, 46)
                assert im.getpixel((x, y)) == expected, (w, mode, x, y, expected, im.getpixel((x, y)))
                pixels += 1
        if mode == 'settings' and w == 770:
            # No inherited six-icon phone deck may bleed through the
            # desktop's two buttons in the tightest 275px content pane.
            for y in range(708, 748):
                for x in range(left + 124, left + 180):
                    assert im.getpixel((x, y)) == (26, 29, 33), ('composer overlap', x, y)
                    pixels += 1
print(f'desktop reference: 27 images, {pixels} pixels; tolerance 0px / 0 RGB')
