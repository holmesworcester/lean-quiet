#!/usr/bin/env python3
"""Builds assets/emoji.bin from Noto Color Emoji: every emoji the font
draws, singles and sequences (skin tones, ZWJ families and professions,
flags, keycaps), as colour pictures at the text's size.

Singles come from the font's character map, sequences from its ligature
substitutions (GSUB); each picture is the font's own bitmap (136 x 128),
resampled (Lanczos) to `size` pixels high and stored as QOI (RGBA, not
premultiplied).

Unicode's presentation rules decide when a single character is drawn as
an emoji: those with Emoji_Presentation always; other emoji characters (©,
♥, ☀) only when followed by VS16 (U+FE0F); digits, # and * only inside
keycap sequences.

Layout (little-endian):
  "QEMJ", count, size, then per entry (sorted by code points): a byte n,
  n code points (words), a flag byte (1: emoji by default; 0: only with
  VS16), width (half-word), offset and length of its QOI in the data
  (words); then the data.

    PYTHONPATH=<fonttools> python3 tools/emoji.py NotoColorEmoji.ttf \\
      emoji-data.txt assets/emoji.bin 48
"""

import io
import struct
import sys

from fontTools.ttLib import TTFont
from PIL import Image


def presentation(path):
    out = set()
    for line in open(path, encoding="utf-8"):
        line = line.split("#")[0].strip()
        if not line:
            continue
        rng, prop = [x.strip() for x in line.split(";")]
        if prop != "Emoji_Presentation":
            continue
        lo, _, hi = rng.partition("..")
        out.update(range(int(lo, 16), int(hi or lo, 16) + 1))
    return out


def ligatures(font):
    """(first glyph, component glyphs) -> ligature glyph, from every
    ligature subtable (extension lookups included)."""
    out = {}
    for lookup in font["GSUB"].table.LookupList.Lookup:
        for st in lookup.SubTable:
            if lookup.LookupType == 7:
                st = st.ExtSubTable
            if not hasattr(st, "ligatures"):
                continue
            for first, ligs in st.ligatures.items():
                for lig in ligs:
                    out[(first, tuple(lig.Component))] = lig.LigGlyph
    return out


def qoi(img):
    """QOI encoding of an RGBA picture (the reference encoder's rules)."""
    w, h = img.size
    px = img.tobytes()
    out = bytearray(b"qoif" + struct.pack(">II", w, h) + bytes([4, 0]))
    index = [(0, 0, 0, 0)] * 64
    prev = (0, 0, 0, 255)
    run = 0
    n = w * h
    for i in range(n):
        p = tuple(px[4 * i:4 * i + 4])
        if p == prev:
            run += 1
            if run == 62 or i == n - 1:
                out.append(0xC0 | (run - 1)); run = 0
            continue
        if run:
            out.append(0xC0 | (run - 1)); run = 0
        hsh = (p[0] * 3 + p[1] * 5 + p[2] * 7 + p[3] * 11) % 64
        if index[hsh] == p:
            out.append(hsh)
        else:
            index[hsh] = p
            if p[3] == prev[3]:
                dr = (p[0] - prev[0] + 128) % 256 - 128
                dg = (p[1] - prev[1] + 128) % 256 - 128
                db = (p[2] - prev[2] + 128) % 256 - 128
                rg, bg = dr - dg, db - dg
                if -2 <= dr <= 1 and -2 <= dg <= 1 and -2 <= db <= 1:
                    out.append(0x40 | (dr + 2) << 4 | (dg + 2) << 2 | (db + 2))
                elif -32 <= dg <= 31 and -8 <= rg <= 7 and -8 <= bg <= 7:
                    out += bytes([0x80 | (dg + 32), (rg + 8) << 4 | (bg + 8)])
                else:
                    out += bytes([254, *p[:3]])
            else:
                out += bytes([255, *p])
        prev = p
    if run:
        out.append(0xC0 | (run - 1))
    return bytes(out + b"\0\0\0\0\0\0\0\1")


def main(ttf, data, dst, size):
    font = TTFont(ttf)
    strike = font["CBDT"].strikeData[0]
    cmap = font.getBestCmap()
    rev = {}
    for cp, g in cmap.items():
        rev.setdefault(g, cp)
    pres = presentation(data)
    seqs = {}
    for cp, g in cmap.items():
        if g in strike and cp >= 0x80:
            seqs[(cp,)] = g
    for (first, comps), lig in ligatures(font).items():
        if lig in strike and first in rev and all(c in rev for c in comps):
            seqs[(rev[first],) + tuple(rev[c] for c in comps)] = lig
    entries = []
    blob = bytearray()
    for seq in sorted(seqs):
        bmp = strike[seqs[seq]]
        bmp.decompile()
        img = Image.open(io.BytesIO(bmp.imageData)).convert("RGBA")
        w = round(img.width * size / img.height)
        img = img.resize((w, size), Image.LANCZOS)
        q = qoi(img)
        flag = 1 if len(seq) > 1 or seq[0] in pres else 0
        entries.append((seq, flag, w, len(blob), len(q)))
        blob += q
    with open(dst, "wb") as out:
        out.write(b"QEMJ" + struct.pack("<II", len(entries), size))
        for seq, flag, w, off, ln in entries:
            out.write(bytes([len(seq)]) + struct.pack("<%dI" % len(seq), *seq))
            out.write(bytes([flag]) + struct.pack("<HII", w, off, ln))
        out.write(blob)
    print(f"{dst}: {len(entries)} emoji ({sum(1 for e in entries if len(e[0]) > 1)} sequences), "
          f"{len(blob)} bytes of pictures at {size} px")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 48)
