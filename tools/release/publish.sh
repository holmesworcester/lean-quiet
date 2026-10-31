#!/usr/bin/env bash
# Publishes out/release/* as GitHub release vX.Y.Z of
# holmesworcester/lean-quiet, at the commit HEAD names, with SHA256SUMS.
# The join page links releases/latest/download/<name>, so asset names stay
# fixed. GH is the gh command to use (default gh-personal, the user's
# personal token; it is a bash function, so this runs it through bash -ic).
#
# usage: tools/release/publish.sh X.Y.Z [notes-file]
set -euo pipefail
cd "$(dirname "$0")/../.."
v=${1:?usage: publish.sh X.Y.Z [notes]}
notes=${2:-}
repo=holmesworcester/lean-quiet
gh=${GH:-gh-personal}
cd out/release
files=(lean-quiet-android.apk lean-quiet-linux-x86_64.tar.gz)
[ -f LeanQuiet-macos.zip ] && files+=(LeanQuiet-macos.zip)
for f in "${files[@]}"; do [ -f "$f" ] || { echo "missing out/release/$f" >&2; exit 1; }; done
sha256sum "${files[@]}" > SHA256SUMS
commit=$(git rev-parse HEAD)
git merge-base --is-ancestor "$commit" origin/main 2>/dev/null || echo "note: $commit is not on origin/main" >&2
args=(release create "v$v" "${files[@]}" SHA256SUMS -R "$repo" --target "$commit" --title "Lean Quiet $v")
if [ -n "$notes" ]; then args+=(--notes-file "$(realpath "../../$notes" 2>/dev/null || realpath "$notes")"); else args+=(--generate-notes); fi
bash -ic "$gh $(printf '%q ' "${args[@]}")" 2>/dev/null
bash -ic "$gh release view v$v -R $repo --json url,assets --jq '.url, (.assets[] | .name + \" \" + (.size|tostring))'" 2>/dev/null
