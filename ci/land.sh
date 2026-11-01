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
# 2. Merge origin/main into HEAD (a conflict stops here: resolve, commit,
#    run it again), build, and refresh the README's links and the vacuity
#    inventory if the merge moved them (a commit of their own).
# 3. The gate (ci/local.sh). A failure stops here, nothing pushed.
# 4. Push HEAD to main, fast-forward only: LAND_PUSH (default
#    `git push origin HEAD:main`; set it to push with your credentials).
set -euo pipefail
cd "$(dirname "$0")/.."
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
git fetch -q origin
if ! git merge-base --is-ancestor origin/main HEAD; then
  git merge --no-edit origin/main ||
    { echo "land: the merge conflicts: resolve, commit, and run ci/land.sh again" >&2; exit 1; }
fi
ci/local.sh build
python3 ci/proof-links.py >/dev/null && python3 ci/vacuity.py --write >/dev/null
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  git commit -qam "README links and vacuity inventory after merging main"
fi
ci/local.sh
git fetch -q origin
git merge-base --is-ancestor origin/main HEAD ||
  { echo "land: main moved without the lock; run ci/land.sh again" >&2; exit 1; }
bash -c "${LAND_PUSH:-git push origin HEAD:main}"
echo "land: main is $(git rev-parse --short HEAD)"
