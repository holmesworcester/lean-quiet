#!/bin/sh
# Noto Core (OFL), pinned local TrueType inputs. Never accesses the network.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
src=${NOTO_FONTS:-/usr/share/fonts/truetype/noto}
mkdir -p "$root/assets"
while read -r hash name; do
  if ! echo "$hash  $root/assets/$name" | sha256sum -c --status >/dev/null 2>&1; then
    echo "$hash  $src/$name" | sha256sum -c --status
    cp "$src/$name" "$root/assets/$name"
  fi
done < "$root/tools/noto.sha256"
cp "$root/tools/NOTO-LICENSE.txt" "$root/assets/NOTO-LICENSE.txt"
