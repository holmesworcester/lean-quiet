#!/usr/bin/env bash
# Publishes the join page: builds the site (site/build.py, which takes the
# same --mac-url / --testflight-url options) and commits it as the next
# commit of the gh-pages branch of holmesworcester/lean-quiet, which
# GitHub Pages serves at https://holmesworcester.github.io/lean-quiet/
# (the join page: .../join#<invite>). Pushes with the user's personal
# token (gh-personal, a bash function, as a git credential helper), and
# turns Pages on for gh-pages if it is off.
set -euo pipefail
cd "$(dirname "$0")/.."
repo=holmesworcester/lean-quiet
python3 site/build.py out/site "$@" >/dev/null
cred=(-c credential.helper= -c "credential.helper=!bash -ic 'gh-personal auth git-credential \"\$@\"' 2>/dev/null --")
git "${cred[@]}" fetch -q origin gh-pages 2>/dev/null || true
parent=$(git rev-parse -q --verify refs/remotes/origin/gh-pages || true)
idx=$(mktemp "${TMPDIR:-/tmp}/lq-pages-index.XXXXXX")
trap 'rm -f "$idx"' EXIT
GIT_INDEX_FILE=$idx git --work-tree=out/site add -A -f .
tree=$(GIT_INDEX_FILE=$idx git write-tree)
if [ -n "$parent" ] && [ "$(git rev-parse "$parent^{tree}")" = "$tree" ]; then
  echo "gh-pages already has this site ($parent)"
else
  commit=$(git commit-tree "$tree" ${parent:+-p "$parent"} -m "Join page from $(git rev-parse --short HEAD)")
  git "${cred[@]}" push -q origin "$commit:refs/heads/gh-pages"
  echo "gh-pages: $commit"
fi
if ! bash -ic "gh-personal api repos/$repo/pages >/dev/null" 2>/dev/null; then
  bash -ic "gh-personal api -X POST repos/$repo/pages -f 'source[branch]=gh-pages' -f 'source[path]=/' --jq .html_url" 2>/dev/null ||
    { echo "could not turn on Pages: Settings > Pages > Deploy from a branch > gh-pages / (root)" >&2; exit 1; }
fi
echo "https://holmesworcester.github.io/lean-quiet/join"
