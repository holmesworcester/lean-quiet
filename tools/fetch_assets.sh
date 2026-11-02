#!/bin/sh
# Fetches the app's data into assets/, each source pinned by sha256: six
# public-domain or CC0 photos (tools/photos.tsv) as the chaos generator's,
# scaled to QOI by tools/photos.py; GNU Unifont 18.0.01, built into
# assets/font.bin by tools/font.py; Noto Color Emoji and Unicode's emoji
# data into emoji.bin; then the Noto and CJK fonts (tools/noto_assets.sh).
# Where each file comes from, and its licence: tools/third_party/NOTICE.txt.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$root/assets"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/quiet-assets.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
# fontTools reads the fonts; Pillow (its wheel carries its own libjpeg-turbo)
# decodes and scales the photos, the same bytes every time.
python3 -m pip install -q --target "$tmp/py" fonttools==4.68.0 pillow==12.1.1
mkdir -p "$tmp/photos"
grep -v '^#' "$root/tools/photos.tsv" | while IFS="$(printf '\t')" read -r i hash _box url; do
  curl --proto '=https' -fsSL -A 'lean-quiet-assets (https://github.com/holmesworcester/lean-quiet)' -o "$tmp/photos/$i.jpg" "$url"
  echo "$hash  $tmp/photos/$i.jpg" | sha256sum -c - >/dev/null
done
PYTHONPATH="$tmp/py" python3 "$root/tools/photos.py" "$tmp/photos" "$root/assets"
(cd "$root/assets" && sha256sum -c --quiet "$root/tools/photos.sha256")
curl --proto '=https' -fsSL -o "$tmp/unifont.hex.gz" https://ftp.gnu.org/gnu/unifont/unifont-18.0.01/unifont_all-18.0.01.hex.gz
echo "14c96e497466a82e46cf20032ce510e186bdc8658c9158e2290f452cda9bc498  $tmp/unifont.hex.gz" | sha256sum -c - >/dev/null
python3 "$root/tools/font.py" "$tmp/unifont.hex.gz" "$root/assets/font.bin" 3
# Colour emoji: Noto Color Emoji 2.051 (OFL) and Unicode 16's emoji data,
# read with fontTools.
curl --proto '=https' -fsSL -o "$tmp/noto.ttf" https://github.com/googlefonts/noto-emoji/raw/v2.051/fonts/NotoColorEmoji.ttf
echo "72a635cb3d2f3524c51620cdde406b217204e8a6a06c6a096ff8ed4b5fd6e27b  $tmp/noto.ttf" | sha256sum -c - >/dev/null
curl --proto '=https' -fsSL -o "$tmp/emoji-data.txt" https://www.unicode.org/Public/16.0.0/ucd/emoji/emoji-data.txt
echo "f1365a5173eee18e1f98b240cdc492e84a25f1ce7e0c9d1094eb29c41a22696a  $tmp/emoji-data.txt" | sha256sum -c - >/dev/null
PYTHONPATH="$tmp/py" python3 "$root/tools/emoji.py" "$tmp/noto.ttf" "$tmp/emoji-data.txt" "$root/assets/emoji.bin" 48
# The reaction catalogue: libquiet's emoji list (app/src/emoji-data.json at
# main 38a909706, from emojibase-data 17.0.0), converted by tools/picker.py.
cp "$root/tools/third_party/picker.txt" "$root/assets/picker.txt"

# Local Noto Core and CJK are installed after the pinned CJK inputs below.

# Google Fonts glyf variable sources, pinned at commit
# 9b59ea9f333c5b8a99fa44e2a698496d6cde5b8e. Exact URLs and hashes live in
# cjk_fonts.tsv (NotoSans{SC,TC,JP,KR}%5Bwght%5D.ttf). Prefer local copies;
# downloads, when needed by this online fetch command, stay in its temp dir.
cjk_local=${CJK_FONTS:-/mnt/storage/holmes-wt/lq-tonight/fonts}
mkdir -p "$tmp/cjk"
while read -r hash name url; do
  if [ -f "$cjk_local/$name" ]; then cp "$cjk_local/$name" "$tmp/cjk/$name"
  else curl --proto '=https' -fsSL -o "$tmp/cjk/$name" "$url"; fi
  echo "$hash  $tmp/cjk/$name" | sha256sum -c - >/dev/null
done < "$root/tools/cjk_fonts.tsv"
CJK_PYTHON="$tmp/py" CJK_FONTS="$tmp/cjk" "$root/tools/noto_assets.sh"
