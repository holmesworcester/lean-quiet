#!/bin/sh
# Fetches the independent tools for tests/qr/xcheck.sh without root:
# qrencode and zbarimg from the distribution's packages (apt-get download,
# unpacked with dpkg -x; their libraries libqrencode4 and libzbar0 must be
# installed), and segno and qrcodegen (pure Python) from PyPI.
# Into out/xtools.
set -eu
cd "$(dirname "$0")/../.."
x=out/xtools
mkdir -p "$x/debs"
if ! [ -x "$x/root/usr/bin/qrencode" ] || ! [ -x "$x/root/usr/bin/zbarimg" ]; then
  (cd "$x/debs" && apt-get download qrencode zbar-tools >/dev/null)
  for d in "$x"/debs/*.deb; do dpkg -x "$d" "$x/root"; done
fi
[ -f "$x/py/qrcodegen.py" ] && [ -d "$x/py/segno" ] ||
  python3 -m pip install --quiet --target "$x/py" segno qrcodegen
echo "tools in $x"
