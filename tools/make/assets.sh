#!/bin/sh
# Puts the app's data (fonts, emoji, glyphs, photos) in assets/ for
# `make install`. It downloads the pinned tarball (tools/make/assets.pin),
# checks its sha256 before opening it and every file against
# tools/make/assets.sha256 after, then moves the files into place. If the
# tarball can't be had or doesn't check out, it builds the data from its
# sources with tools/fetch_assets.sh instead (slower, and needs more).
#
#   LQ_ASSETS_URL=...      download from here (https:// or file://), not
#                          from the GitHub release the pin names
#   LQ_ASSETS_FALLBACK=0   fail rather than run tools/fetch_assets.sh
#   LQ_ASSETS_DIR, LQ_ASSETS_PIN, LQ_ASSETS_MANIFEST
#                          other places for assets/, the pin and the
#                          per-file list (tests/make/assets_test.sh)
# Portable sh: Linux and macOS.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
top=$(cd "$here/../.." && pwd)
pin=${LQ_ASSETS_PIN:-$here/assets.pin}
manifest=${LQ_ASSETS_MANIFEST:-$here/assets.sha256}
dest=${LQ_ASSETS_DIR:-$top/assets}
. "$pin"
url=${LQ_ASSETS_URL:-https://github.com/$LQ_ASSETS_REPO/releases/download/$LQ_ASSETS_TAG/$LQ_ASSETS_NAME}

say() { printf '==> %s\n' "$*"; }
warn() { printf 'assets: %s\n' "$*" >&2; }
sha256() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$@"; else shasum -a 256 "$@"; fi; }
# every file of the list, with its pinned hash, is in $1
complete() { [ -d "$1" ] && (cd "$1" && sha256 -c --status "$manifest") 2>/dev/null; }

if complete "$dest"; then say "assets: all $(wc -l < "$manifest" | tr -d ' ') files in place"; exit 0; fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/lq-assets.XXXXXX")
trap 'rm -rf "$tmp"' EXIT INT TERM

fetch() {
  say "assets: downloading $url"
  curl --proto '=https,file' -fsSL --retry 3 -o "$tmp/assets.tar.gz" "$url" || { warn "could not download $url"; return 1; }
  got=$(sha256 "$tmp/assets.tar.gz" | cut -d' ' -f1)
  if [ "$got" != "$LQ_ASSETS_SHA256" ]; then
    warn "rejected $url: its sha256 is $got, not the pinned $LQ_ASSETS_SHA256"
    return 1
  fi
  mkdir "$tmp/x"
  tar -xzf "$tmp/assets.tar.gz" -C "$tmp/x"
  complete "$tmp/x/assets" || { warn "rejected $url: its files don't match $manifest"; return 1; }
  mkdir -p "$dest"
  while read -r _ name; do
    cp "$tmp/x/assets/$name" "$dest/$name.new" && mv -f "$dest/$name.new" "$dest/$name"
  done < "$manifest"
  complete "$dest" || { warn "the files in $dest don't match $manifest after unpacking"; return 1; }
  say "assets: $(wc -l < "$manifest" | tr -d ' ') files in $dest"
}

fetch && exit 0
if [ "${LQ_ASSETS_FALLBACK:-1}" = 0 ] || [ "$dest" != "$top/assets" ]; then exit 1; fi
say "assets: building them from their sources instead (tools/fetch_assets.sh)"
if ! "$top/tools/fetch_assets.sh"; then
  warn "tools/fetch_assets.sh failed. It needs network access, unzip, python3 with pip,"
  warn "librsvg and Cairo, and the system Noto fonts it pins (Ubuntu 24.04's fonts-noto-core)."
  exit 1
fi
complete "$dest" || warn "the built files differ from $manifest; the build checks them again"
