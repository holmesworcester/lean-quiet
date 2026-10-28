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
python3 "$root/tools/font.py" "$tmp/unifont.hex.gz" "$root/assets/font.bin"
