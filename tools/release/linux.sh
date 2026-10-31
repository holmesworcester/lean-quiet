#!/usr/bin/env bash
# The Linux release, x86-64, X11 (Wayland desktops run it through
# XWayland), glibc 2.34 or newer:
# - lean-quiet-linux-amd64.deb (Debian, Ubuntu and their kin; a fixed name,
#   as the join page links releases/latest/download/<name>):
#   /opt/lean-quiet, the launcher /usr/bin/lean-quiet and a desktop entry
#   for x-scheme-handler/leanquiet, so leanquiet:// links open it once it is
#   installed (desktop-file-utils' trigger rebuilds mimeinfo.cache);
# - lean-quiet-linux-x86_64.tar.gz (any distribution): one folder,
#   lean-quiet/, with the program, its assets, install.sh (into ~/.local,
#   and registers the link handler) and the icon.
#
# usage: tools/release/linux.sh X.Y.Z
set -euo pipefail
cd "$(dirname "$0")/../.."
v=${1:?usage: linux.sh X.Y.Z}
[[ $v =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo "version is X.Y.Z" >&2; exit 2; }
[ -f assets/font.bin ] || tools/fetch_assets.sh
platforms/linux/build.sh
rel=out/release; st=$rel/linux
rm -rf "$st"; mkdir -p "$st"
bin=$st/lean-quiet.bin
install -m 755 .lake/build/bin/linux "$bin"; strip "$bin"
# glibc no newer than 2.34 (Ubuntu 22.04, Debian 12 and later)
newest=$(objdump -T "$bin" | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1)
[ "$(printf '%s\nGLIBC_2.34\n' "$newest" | sort -V | tail -1)" = GLIBC_2.34 ] || { echo "needs $newest" >&2; exit 1; }

# The tarball.
app=$st/tar/lean-quiet; mkdir -p "$app"
cp "$bin" "$app/lean-quiet"
rsync -a assets/ "$app/assets/"
install -m 755 platforms/linux/install.sh "$app/install.sh"
install -m 644 platforms/linux/lean-quiet.svg "$app/lean-quiet.svg"
echo "$v $(git rev-parse --short HEAD)" > "$app/VERSION"
cat > "$app/README.txt" <<TXT
Lean Quiet $v for Linux (x86-64; X11 or XWayland; glibc 2.34 or newer;
libxcb, libxcb-shm and libxcb-sync; xdg-utils for invite links).

  lean-quiet/install.sh   installs into ~/.local and makes leanquiet://
                          invite links open in Lean Quiet
On Debian or Ubuntu, the .deb does the same for every user.

Source: https://github.com/holmesworcester/lean-quiet
TXT
tar -C "$st/tar" --owner=0 --group=0 -czf "$rel/lean-quiet-linux-x86_64.tar.gz" lean-quiet

# The .deb.
d=$st/deb
mkdir -p "$d/DEBIAN" "$d/opt/lean-quiet" "$d/usr/bin" "$d/usr/share/applications" \
  "$d/usr/share/icons/hicolor/scalable/apps" "$d/usr/share/doc/lean-quiet"
cp "$bin" "$d/opt/lean-quiet/lean-quiet"
rsync -a assets/ "$d/opt/lean-quiet/assets/"
install -m 644 platforms/linux/lean-quiet.svg "$d/usr/share/icons/hicolor/scalable/apps/lean-quiet.svg"
cat > "$d/usr/bin/lean-quiet" <<'SH'
#!/bin/sh
# Lean Quiet. The app reads assets/ relative to its working directory, so it
# runs from /opt/lean-quiet; the data (database, zoom level, log) stays in
# XDG data. A leanquiet:// link argument passes through (to the running
# copy, if there is one).
data="${XDG_DATA_HOME:-$HOME/.local/share}/lean-quiet"
mkdir -p "$data"
[ -t 2 ] || exec 2>>"$data/lean-quiet.log"
[ -t 1 ] || exec 1>&2
cd /opt/lean-quiet || exit 1
QUIET_DB="${QUIET_DB:-$data/quiet.db}" exec ./lean-quiet "$@"
SH
chmod 755 "$d/usr/bin/lean-quiet"
cat > "$d/usr/share/applications/lean-quiet.desktop" <<'DESK'
[Desktop Entry]
Type=Application
Name=Lean Quiet
GenericName=Private chat
Comment=Quiet in Lean: peer-to-peer team chat
Exec=/usr/bin/lean-quiet %u
Icon=lean-quiet
Terminal=false
Categories=Network;Chat;InstantMessaging;
Keywords=quiet;chat;lean;
MimeType=x-scheme-handler/leanquiet;
StartupWMClass=lean-quiet
DESK
cp assets/NOTO-LICENSE.txt "$d/usr/share/doc/lean-quiet/NOTO-LICENSE.txt"
printf 'Lean Quiet %s\nSource: https://github.com/holmesworcester/lean-quiet\nFonts: see NOTO-LICENSE.txt\n' "$v" > "$d/usr/share/doc/lean-quiet/copyright"
cat > "$d/DEBIAN/control" <<CTL
Package: lean-quiet
Version: $v
Architecture: amd64
Maintainer: Holmes Wilson <holmesworcester@users.noreply.github.com>
Installed-Size: $(du -sk "$d" | cut -f1)
Depends: libc6 (>= 2.34), libxcb1, libxcb-shm0, libxcb-sync1
Recommends: xdg-utils, desktop-file-utils
Section: net
Priority: optional
Homepage: https://holmesworcester.github.io/lean-quiet/join
Description: local-first, peer-to-peer, end-to-end encrypted chat in Lean
 Lean Quiet is a chat app written mostly in Lean, with proofs about the
 code that runs. Invite links (leanquiet://) open in it.
CTL
find "$d" -type d -exec chmod 755 {} +
deb=$rel/lean-quiet-linux-amd64.deb
dpkg-deb --root-owner-group -Zxz --build "$d" "$deb" >/dev/null
# What was built: the entry claims leanquiet:// with an unquoted Exec and %u.
dpkg-deb -I "$deb" | grep -q "Version: $v"
dpkg-deb -c "$deb" | grep -q './usr/share/applications/lean-quiet.desktop'
dpkg-deb --fsys-tarfile "$deb" | tar -xO ./usr/share/applications/lean-quiet.desktop |
  grep -qx 'Exec=/usr/bin/lean-quiet %u'
desktop-file-validate "$d/usr/share/applications/lean-quiet.desktop"
echo "release $v: $deb ($(du -h "$deb" | cut -f1)), $rel/lean-quiet-linux-x86_64.tar.gz ($(du -h "$rel/lean-quiet-linux-x86_64.tar.gz" | cut -f1)); needs $newest"
