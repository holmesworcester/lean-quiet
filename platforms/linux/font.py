#!/usr/bin/env python3
"""Reduce the existing QFNT to 16px for desktop, offline. No new font dependency."""
import pathlib
import struct
import sys

src = pathlib.Path(sys.argv[1]).read_bytes()
cell = struct.unpack_from('<I', src, 4)[0]
assert src[:4] == b'QFNT' and cell in (32, 48, 64)
end = 8 + 4 * 0x20000
out = bytearray(b'QFNT' + struct.pack('<I', 16) + bytes(end - 8))
for cp in range(0x20000):
    entry = struct.unpack_from('<I', src, 8 + cp * 4)[0]
    if not entry:
        continue
    wide = bool(entry & 0x80000000)
    width = cell if wide else cell // 2
    at = end + (entry & 0x7fffffff) - 1
    struct.pack_into('<I', out, 8 + cp * 4, len(out) - end + 1 | (entry & 0x80000000))
    for y in range(16):
        row = int.from_bytes(src[at + (y * cell // 16) * (width // 8):at + (y * cell // 16 + 1) * (width // 8)], 'big')
        bits = 0
        for x in range(16 if wide else 8):
            bits = (bits << 1) | ((row >> (width - 1 - x * cell // 16)) & 1)
        out.extend(bits.to_bytes(2 if wide else 1, 'big'))
path = pathlib.Path(sys.argv[2])
path.parent.mkdir(parents=True, exist_ok=True)
path.write_bytes(out)
