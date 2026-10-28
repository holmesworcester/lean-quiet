#!/bin/sh
# Fetches the app's data into assets/: the QOI test images (qoiformat.org,
# pinned by sha256) as the chaos generator's photos, and GNU Unifont 18.0.01
# (pinned by sha256), built into assets/font.bin by tools/font.py.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$root/assets"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/quiet-assets.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
curl --proto '=https' -fsSL -o "$tmp/images.zip" https://qoiformat.org/qoi_test_images.zip
echo "bd557fb208222478d9eefcae59fb473d10e047fd7a8885fcff48861f86599165  $tmp/images.zip" | sha256sum -c - >/dev/null
(cd "$tmp" && unzip -q images.zip)
i=0
for name in kodim23 dice qoi_logo testcard_rgba wikipedia_008 kodim10; do
  cp "$tmp/qoi_test_images/$name.qoi" "$root/assets/$i.qoi"
  i=$((i + 1))
done
curl --proto '=https' -fsSL -o "$tmp/unifont.hex.gz" https://ftp.gnu.org/gnu/unifont/unifont-18.0.01/unifont_all-18.0.01.hex.gz
echo "14c96e497466a82e46cf20032ce510e186bdc8658c9158e2290f452cda9bc498  $tmp/unifont.hex.gz" | sha256sum -c - >/dev/null
python3 "$root/tools/font.py" "$tmp/unifont.hex.gz" "$root/assets/font.bin" 3
# Colour emoji: Noto Color Emoji 2.051 (OFL) and Unicode 16's emoji data,
# read with fontTools (pip install --target "$tmp/py" fonttools).
curl --proto '=https' -fsSL -o "$tmp/noto.ttf" https://github.com/googlefonts/noto-emoji/raw/v2.051/fonts/NotoColorEmoji.ttf
curl --proto '=https' -fsSL -o "$tmp/emoji-data.txt" https://www.unicode.org/Public/16.0.0/ucd/emoji/emoji-data.txt
echo "f1365a5173eee18e1f98b240cdc492e84a25f1ce7e0c9d1094eb29c41a22696a  $tmp/emoji-data.txt" | sha256sum -c - >/dev/null
python3 -m pip install -q --target "$tmp/py" fonttools
PYTHONPATH="$tmp/py" python3 "$root/tools/emoji.py" "$tmp/noto.ttf" "$tmp/emoji-data.txt" "$root/assets/emoji.bin" 48
