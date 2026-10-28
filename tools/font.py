#!/usr/bin/env python3
"""Builds assets/font.bin from GNU Unifont's .hex: the Basic Multilingual
Plane (every living script) and the emoji and symbols of plane 1, each
8 x 16 or 16 x 16 glyph smoothed to 2x (Scale2x: a 32-pixel cell), 3x
(Scale3x: 48 pixels, the default: about 18 dp on a 420-dpi phone) or 4x
(Scale2x twice: 64 pixels).

Layout (little-endian):
  "QFNT", the cell's height in pixels (a word), then 0x20000 words, one
  per code point: 0 if the font lacks it, else 1 + the offset of its rows
  in the data (bit 31: wide); then the data: `cell` rows per glyph, each
  cell/16 bytes (narrow, cell/2 pixels) or cell/8 (wide, cell pixels),
  the leftmost pixel in the row's top bit, a row's bytes most significant
  first.

    python3 tools/font.py unifont_all-18.0.01.hex.gz assets/font.bin [2|3|4]

Emoji are not drawn from this font: tools/emoji.py builds colour ones.
"""

import gzip
import struct
import sys

LIMIT = 0x20000


def keep(cp):
    """The Basic Multilingual Plane (every living script), and from the
    supplementary plane only its symbols and emoji (U+1F000..U+1FAFF):
    the historic scripts there would triple the file."""
    return cp < 0x10000 or 0x1F000 <= cp < 0x1FB00


def scale3x(g):
    """Scale3x (AdvMAME3x) on a 1-bit grid: each pixel becomes a 3 x 3
    block whose edges and corners take a neighbour's value where the
    neighbours agree, so diagonals stay smooth at three times the size."""
    h, w = len(g), len(g[0])
    at = lambda y, x: g[y][x] if 0 <= y < h and 0 <= x < w else 0
    o = [[0] * (3 * w) for _ in range(3 * h)]
    for y in range(h):
        for x in range(w):
            A, B, C = at(y - 1, x - 1), at(y - 1, x), at(y - 1, x + 1)
            D, E, F = at(y, x - 1), at(y, x), at(y, x + 1)
            G, H, I = at(y + 1, x - 1), at(y + 1, x), at(y + 1, x + 1)
            e = [E] * 9
            if B != H and D != F:
                e[0] = D if D == B else E
                e[1] = B if (D == B and E != C) or (B == F and E != A) else E
                e[2] = F if B == F else E
                e[3] = D if (D == B and E != G) or (D == H and E != A) else E
                e[5] = F if (B == F and E != I) or (H == F and E != C) else E
                e[6] = D if D == H else E
                e[7] = H if (D == H and E != I) or (H == F and E != G) else E
                e[8] = F if H == F else E
            for k in range(9):
                o[3 * y + k // 3][3 * x + k % 3] = e[k]
    return o


def scale2x(g):
    """Scale2x (EPX) on a 1-bit grid: straight strokes stay as they were,
    45-degree staircases become smooth diagonals."""
    h, w = len(g), len(g[0])
    at = lambda y, x: g[y][x] if 0 <= y < h and 0 <= x < w else 0
    o = [[0] * (2 * w) for _ in range(2 * h)]
    for y in range(h):
        for x in range(w):
            p, a, b, c, d = at(y, x), at(y - 1, x), at(y, x + 1), at(y, x - 1), at(y + 1, x)
            e = [p, p, p, p]
            if c == a and c != d and a != b:
                e[0] = a
            if a == b and a != c and b != d:
                e[1] = b
            if d == c and d != b and c != a:
                e[2] = c
            if b == d and b != a and d != c:
                e[3] = d
            o[2 * y][2 * x], o[2 * y][2 * x + 1] = e[0], e[1]
            o[2 * y + 1][2 * x], o[2 * y + 1][2 * x + 1] = e[2], e[3]
    return o


def main(src, dst, scale=3):
    table = [0] * LIMIT
    data = bytearray()
    opener = gzip.open if src.endswith(".gz") else open
    with opener(src, "rt") as f:
        for line in f:
            cp, hexs = line.strip().split(":")
            cp = int(cp, 16)
            if not keep(cp):
                continue
            w = len(hexs) // 4  # 32 hex digits: 8 wide; 64: 16 wide
            digits = w // 4
            grid = []
            for r in range(16):
                row = int(hexs[r * digits:(r + 1) * digits], 16)
                grid.append([(row >> (w - 1 - i)) & 1 for i in range(w)])
            big = scale3x(grid) if scale == 3 else scale2x(grid)
            if scale == 4:
                big = scale2x(big)
            wide = w == 16
            table[cp] = (len(data) + 1) | (0x80000000 if wide else 0)
            for row in big:
                v = 0
                for bit in row:
                    v = (v << 1) | bit
                data += v.to_bytes((16 * scale if wide else 8 * scale) // 8, "big")
    with open(dst, "wb") as out:
        out.write(b"QFNT")
        out.write(struct.pack("<I", 16 * scale))
        out.write(struct.pack("<%dI" % LIMIT, *table))
        out.write(data)
    print(f"{dst}: {sum(1 for t in table if t)} glyphs, {8 + 4 * LIMIT + len(data)} bytes, cell {16 * scale}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 3)
