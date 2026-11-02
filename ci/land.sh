#!/usr/bin/env bash
# Land this branch on main, one landing at a time on this box: a lock in
# $TMPDIR is held while main is merged in, the result gated and pushed, so
# no gate is wasted on a main that moved under it. Waiting for the lock
# costs nothing; run it in the background and keep working.
#
#   ci/land.sh
#
# 1. Wait for the lock ($TMPDIR/lean-quiet-land.lock; flock frees it if
#    the holder dies).
# 2. Merge origin/main into HEAD (a conflict stops here, but for README's
#    generated lines, ci/readme-merge.py: resolve, commit, run it again),
#    build, and refresh the README's links and the vacuity inventory if
#    the merge moved them (a commit of their own).
# 3. The gate (ci/local.sh). A failure stops here, nothing pushed.
# 4. Push HEAD to main, fast-forward only: LAND_PUSH (default
#    `git push origin HEAD:main`; set it to push with your credentials).
#    Then save the build for the next landing to start from.
set -euo pipefail
# The merge below may change this very file while bash reads it (bash reads
# a script as it runs): run from a copy of it that nothing changes.
if [ -z "${LAND_ROOT:-}" ]; then
  LAND_ROOT=$(cd "$(dirname "$0")/.." && pwd)
  export LAND_ROOT
  copy=$(mktemp "${TMPDIR:-/mnt/storage/holmes-tmp}/land.XXXXXX")
  cp "$0" "$copy"
  exec bash "$copy" "$@"
fi
trap 'rm -f -- "$0"' EXIT
cd "$LAND_ROOT"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
lock=$TMPDIR/lean-quiet-land.lock
[ -z "$(git status --porcelain --untracked-files=no)" ] ||
  { echo "land: commit your changes first" >&2; exit 1; }
exec 9>>"$lock"
if ! flock -n 9; then
  echo "land: waiting for the landing lock ($lock)"
  flock 9
fi
echo "land: $(git rev-parse --short HEAD) holds the lock"
# Fetch main alone, again on failure: the worktrees share one repository's
# remote refs, and another worktree fetching at the same moment makes a
# whole-remote fetch fail (holmes-71).
fetch_main() {
  local i
  for i in 1 2 3 4 5; do
    git fetch -q origin +refs/heads/main:refs/remotes/origin/main && return 0
    sleep "$i"
  done
  echo "land: could not fetch main" >&2; return 1
}
fetch_main
if ! git merge-base --is-ancestor origin/main HEAD; then
  # no rerere: a recorded resolution (anyone's, of running code too) would be
  # replayed into the tree without markers; land.sh resolves only generated
  # lines itself and stops on anything else for a person to see
  if ! git -c rerere.enabled=false merge --no-edit origin/main; then
    # README's generated lines (links, table rows) conflict on most merges:
    # main's are taken, and written again below; anything else stops here
    if [ "$(git diff --name-only --diff-filter=U)" = README.md ] && python3 ci/readme-merge.py; then
      git add README.md && git commit -q --no-edit
    else
      echo "land: the merge conflicts: resolve, commit, and run ci/land.sh again" >&2; exit 1
    fi
  fi
fi
# Start from the build of main's last landing ($TMPDIR/lean-quiet-main-build,
# saved below): Lake rebuilds by content hash, so only what this branch
# changes is built again, not everything main moved since this tree last
# built (a landing's merge rebuild took 50 minutes under load without it).
# --update keeps this tree's own newer outputs.
cache=$TMPDIR/lean-quiet-main-build
if [ -d "$cache/build" ]; then
  echo "land: starting from the build of main at $(cat "$cache/commit" 2>/dev/null)"
  rsync -a --update "$cache/build/" .lake/build/
fi
ci/local.sh build
python3 ci/proof-links.py >/dev/null && python3 ci/vacuity.py --write >/dev/null
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  git commit -qam "README links and vacuity inventory after merging main"
fi
ci/local.sh
fetch_main
git merge-base --is-ancestor origin/main HEAD ||
  { echo "land: main moved without the lock; run ci/land.sh again" >&2; exit 1; }
bash -c "${LAND_PUSH:-git push origin HEAD:main}"
echo "land: main is $(git rev-parse --short HEAD)"
# the next landing starts from this build (still under the lock)
mkdir -p "$cache"
rsync -a --delete .lake/build/ "$cache/build/" && git rev-parse --short HEAD > "$cache/commit"
echo "land: saved this build for the next landing"
