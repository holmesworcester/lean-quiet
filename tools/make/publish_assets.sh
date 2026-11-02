#!/usr/bin/env bash
# Publishes the pinned assets tarball (tools/make/assets.pin, packed into
# out/make by tools/make/assets.py pack) as GitHub release $LQ_ASSETS_TAG
# of holmesworcester/lean-quiet, then downloads it back and checks its
# sha256. The release is never marked latest: the join page links
# releases/latest/download/<name>. GH is the gh command to use (default
# gh-personal, the user's personal token; a bash function, so this runs it
# through bash -ic, as tools/release/publish.sh does).
#
# usage: tools/make/publish_assets.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
. tools/make/assets.pin
f=out/make/$LQ_ASSETS_NAME
[ -f "$f" ] || { echo "no $f (tools/make/assets.py pack)" >&2; exit 1; }
[ "$(sha256sum "$f" | cut -d' ' -f1)" = "$LQ_ASSETS_SHA256" ] || { echo "$f does not have the pinned sha256" >&2; exit 1; }
python3 tools/make/assets.py check
gh=${GH:-gh-personal}
args=(release create "$LQ_ASSETS_TAG" "$f" -R "$LQ_ASSETS_REPO" --latest=false
  --title "Assets $LQ_ASSETS_TAG"
  --notes "The app's data (fonts, emoji, glyphs, photos) that make install downloads. sha256 $LQ_ASSETS_SHA256. Packed by tools/make/assets.py.")
bash -ic "$gh $(printf '%q ' "${args[@]}")" 2>/dev/null
url=https://github.com/$LQ_ASSETS_REPO/releases/download/$LQ_ASSETS_TAG/$LQ_ASSETS_NAME
got=$(curl --proto '=https' --proto-redir '=https' -fsSL "$url" | sha256sum | cut -d' ' -f1)
[ "$got" = "$LQ_ASSETS_SHA256" ] || { echo "downloaded $url has sha256 $got, not $LQ_ASSETS_SHA256" >&2; exit 1; }
echo "published $url (sha256 checked)"
