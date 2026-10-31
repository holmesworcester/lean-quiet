#!/usr/bin/env bash
# The Linux release: x86-64, X11 (Wayland desktops run it through
# XWayland). A tarball holding one folder, lean-quiet/: the program, its
# assets, install.sh (installs into ~/.local and makes the browser hand
# leanquiet:// links to it) and the icon.
#
# usage: tools/release/linux.sh X.Y.Z   -> out/release/lean-quiet-linux-x86_64.tar.gz
set -euo pipefail
cd "$(dirname "$0")/../.."
v=${1:?usage: linux.sh X.Y.Z}
[[ $v =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo "version is X.Y.Z" >&2; exit 2; }
[ -f assets/font.bin ] || tools/fetch_assets.sh
platforms/linux/build.sh
for f in platforms/linux/install.sh platforms/linux/lean-quiet.svg; do
  [ -f "$f" ] || { echo "missing $f" >&2; exit 1; }
done
st=out/release/linux; app=$st/lean-quiet
rm -rf "$st"; mkdir -p "$app"
install -m 755 .lake/build/bin/linux "$app/lean-quiet"
strip "$app/lean-quiet"
rsync -a --delete assets/ "$app/assets/"
install -m 755 platforms/linux/install.sh "$app/install.sh"
install -m 644 platforms/linux/lean-quiet.svg "$app/lean-quiet.svg"
echo "$v $(git rev-parse --short HEAD)" > "$app/VERSION"
cat > "$app/README.txt" <<TXT
Lean Quiet $v for Linux (x86-64, X11 or XWayland; glibc 2.34 or newer;
libxcb, libxcb-shm and libxcb-sync).

  lean-quiet/install.sh     installs into ~/.local and lets your browser
                            open leanquiet:// invite links in Lean Quiet
  lean-quiet/lean-quiet     runs it from here (run it from this folder)

Source: https://github.com/holmesworcester/lean-quiet
TXT
# glibc no newer than 2.34 (Ubuntu 22.04, Debian 12 and later)
newest=$(objdump -T "$app/lean-quiet" | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1)
[ "$(printf '%s\nGLIBC_2.34\n' "$newest" | sort -V | tail -1)" = GLIBC_2.34 ] || { echo "needs $newest" >&2; exit 1; }
tar -C "$st" --owner=0 --group=0 -czf out/release/lean-quiet-linux-x86_64.tar.gz lean-quiet
echo "release $v: out/release/lean-quiet-linux-x86_64.tar.gz ($(du -h out/release/lean-quiet-linux-x86_64.tar.gz | cut -f1)), needs $newest"
