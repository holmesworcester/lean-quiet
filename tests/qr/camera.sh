#!/usr/bin/env bash
# The camera suite's frames: the invite link encoded by Lean at L, M, Q and
# H, put into 640x480 frames by tools/distort (perspective, rotation, scale,
# blur, noise, lighting, contrast, occlusion, mirror images). Writes
# out/camera/manifest.tsv (name, frame, payload hex) for qr_check.
# Needs python3 with numpy and Pillow.
set -euo pipefail
cd "$(dirname "$0")/.."
out=out/camera
rm -rf "$out"; mkdir -p "$out/frames"
python3 -c 'import numpy, PIL' 2>/dev/null || {
  echo "camera suite: needs python3 with numpy and Pillow (pip install numpy pillow)"; exit 1; }
# a realistic invite: quiet://join/ and 187 base62 characters (200 bytes)
python3 -c "
import random
r = random.Random(1)
a = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
open('$out/invite', 'w').write('quiet://join/' + ''.join(r.choice(a) for _ in range(187)))"
hex=$(python3 -c "print(open('$out/invite','rb').read().hex())")
syms=()
for e in L M Q H; do
  .lake/build/bin/qr_tool render "$out/sym$e.pgm" $e 1 4 1 auto "$out/invite" >/dev/null
  syms+=("$e=$out/sym$e.pgm")
done
python3 tools/distort/cases.py "$out/cases.tsv" "${syms[@]}" >/dev/null
python3 tools/distort/distort.py "$out/cases.tsv" "$out/frames" >/dev/null
while IFS=$'\t' read -r name _; do
  printf "%s\t%s\t%s\n" "$name" "$PWD/$out/frames/$name.pgm" "$hex"
done < "$out/cases.tsv" > "$out/manifest.tsv"
echo "camera suite: $(wc -l < "$out/manifest.tsv") frames in $out/frames"
