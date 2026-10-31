#!/bin/sh
# Install Lean Quiet for one user, as the handler of leanquiet:// links.
#
#   ./install.sh                    from a release folder holding lean-quiet
#                                   (the `linux` executable), assets/, this
#                                   script and lean-quiet.svg
#   platforms/linux/install.sh      from a repository build: .lake/build/bin/linux
#                                   and assets/ (mise run linux:build)
#
# PREFIX (default ~/.local) receives
#   opt/lean-quiet/{lean-quiet,assets/}    the program
#   bin/lean-quiet                         the launcher
#   share/applications/lean-quiet.desktop  the menu entry, for x-scheme-handler/leanquiet
#   share/icons/hicolor/scalable/apps/lean-quiet.svg
# and xdg-mime makes the entry the default leanquiet:// handler. The data
# (database, zoom level, log) stays in ${XDG_DATA_HOME:-~/.local/share}/lean-quiet.
set -eu
LC_ALL=C; export LC_ALL
here=$(cd "$(dirname "$0")" && pwd)
if [ -f "$here/lean-quiet" ]; then app=$here/lean-quiet assets=$here/assets
else top=$(cd "$here/../.." && pwd); app=$top/.lake/build/bin/linux assets=$top/assets; fi
die() { echo "install.sh: $*" >&2; exit 1; }
[ -x "$app" ] || die "no built app at $app (mise run linux:build)"
[ -f "$assets/font.bin" ] || die "no assets at $assets"
[ -f "$here/lean-quiet.svg" ] || die "no icon at $here/lean-quiet.svg"
prefix=${PREFIX:-$HOME/.local}
case $prefix in /*) ;; *) die "PREFIX must be an absolute path: $prefix" ;; esac
launcher=$prefix/bin/lean-quiet
# xdg-open's generic fallback runs Exec's first word as the command and
# cannot unquote it; a quoted Exec sends the link to the browser instead.
case $launcher in
  *[!A-Za-z0-9/._+@,:=-]*) die "$launcher has a space or another character an unquoted Exec cannot hold (allowed: A-Za-z0-9/._+@,:=-); choose another PREFIX" ;;
esac

opt=$prefix/opt/lean-quiet
mkdir -p "$opt" "$prefix/bin" "$prefix/share/applications" "$prefix/share/icons/hicolor/scalable/apps"
# Renamed into place: a running copy keeps its file.
cp "$app" "$opt/lean-quiet.new" && mv -f "$opt/lean-quiet.new" "$opt/lean-quiet"
rm -rf "$opt/assets.new" && cp -R "$assets" "$opt/assets.new" && rm -rf "$opt/assets" && mv "$opt/assets.new" "$opt/assets"
cp "$here/lean-quiet.svg" "$prefix/share/icons/hicolor/scalable/apps/lean-quiet.svg"

cat > "$launcher.new" <<EOF
#!/bin/sh
# Lean Quiet (Linux desktop). The app reads assets/ relative to its working
# directory, so run from the program folder; keep the data (database, zoom
# level, log) in XDG data. A leanquiet:// link argument passes through.
app="$opt"
data="\${XDG_DATA_HOME:-\$HOME/.local/share}/lean-quiet"
mkdir -p "\$data"
[ -t 2 ] || exec 2>>"\$data/lean-quiet.log"
[ -t 1 ] || exec 1>&2
cd "\$app" || exit 1
QUIET_DB="\${QUIET_DB:-\$data/quiet.db}" exec ./lean-quiet "\$@"
EOF
chmod 755 "$launcher.new" && mv -f "$launcher.new" "$launcher"

cat > "$prefix/share/applications/lean-quiet.desktop" <<EOF
[Desktop Entry]
Type=Application
Name=Lean Quiet
GenericName=Private chat
Comment=Quiet in Lean: peer-to-peer team chat
Exec=$launcher %u
Icon=lean-quiet
Terminal=false
Categories=Network;Chat;InstantMessaging;
Keywords=quiet;chat;lean;
MimeType=x-scheme-handler/leanquiet;
StartupWMClass=lean-quiet
EOF

if command -v update-desktop-database >/dev/null; then update-desktop-database "$prefix/share/applications"
else echo "install.sh: no update-desktop-database (desktop-file-utils); skipped" >&2; fi
command -v xdg-mime >/dev/null || die "xdg-mime (xdg-utils) is needed to register leanquiet:// links"
xdg-mime default lean-quiet.desktop x-scheme-handler/leanquiet
case ":${XDG_DATA_HOME:-$HOME/.local/share}:${XDG_DATA_DIRS:-/usr/local/share:/usr/share}:" in
  *":$prefix/share:"* | *":$prefix/share/:"*) ;;
  *) echo "install.sh: $prefix/share is not on the XDG data path; the menu entry will not be found" >&2 ;;
esac
echo "installed $launcher; leanquiet:// opens $(xdg-mime query default x-scheme-handler/leanquiet)"
