#!/usr/bin/env bash
# The nightly release run: main's head, in a worktree of its own, through
# `ci/local.sh --full` at -j 4 (the box is shared). The night's run log,
# its parts' logs and a summary (exit, time, the parts that failed) go to
# $TMPDIR/lean-quiet-nightly/<date>/, linked as .../latest. A failure the
# landing gate missed is an escape: it becomes a law (docs/CAUGHT.md).
#
#   ci/nightly.sh        (cron: 30 3 * * *; `mise run ci:nightly`)
#
# NIGHTLY_TREE (default /mnt/storage/holmes-wt/lq-nightly) is a worktree
# kept for this run alone: it is reset to main each night.
set -uo pipefail
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH:/usr/local/bin:/usr/bin:/bin"
shell=$(ls -d "$HOME"/.cache/ms-playwright/chromium_headless_shell-*/chrome-headless-shell-linux64/chrome-headless-shell 2>/dev/null | tail -1)
export CHROME=${CHROME:-$shell} PLAYWRIGHT_CHROMIUM_EXECUTABLE=${PLAYWRIGHT_CHROMIUM_EXECUTABLE:-$shell}
export CI=1 WORKSPACE_PORT=${WORKSPACE_PORT:-4199}
repo=$(cd "$(dirname "$0")/.." && pwd)
tree=${NIGHTLY_TREE:-/mnt/storage/holmes-wt/lq-nightly}
night=$TMPDIR/lean-quiet-nightly/$(date +%F)
mkdir -p "$night"
exec 9>>"$TMPDIR/lean-quiet-nightly.lock"
flock -n 9 || { echo "nightly: another nightly run holds the lock" | tee -a "$night/summary"; exit 1; }
git -C "$repo" fetch -q origin +refs/heads/main:refs/remotes/origin/main
[ -d "$tree" ] || git -C "$repo" worktree add -q --detach "$tree" origin/main
cd "$tree" || exit 1
git checkout -q --detach origin/main && git reset -q --hard origin/main
# start from the last landing's build (ci/land.sh saves it)
cache=$TMPDIR/lean-quiet-main-build
if [ -d "$cache/build" ]; then mkdir -p .lake/build && rsync -a --update "$cache/build/" .lake/build/; fi
rm -rf out/ci
start=$(date +%s)
systemd-run --user --scope -q -p MemoryMax=48G -p MemorySwapMax=0 \
  env MISE_TRUSTED_CONFIG_PATHS="$tree" ci/local.sh --full -j "${NIGHTLY_JOBS:-4}" > "$night/run.log" 2>&1
code=$?
{
  echo "nightly $(date +%F) on main $(git rev-parse --short HEAD): exit $code in $(( $(date +%s) - start )) s"
  grep -E '^FAIL' "$night/run.log" || echo "all parts pass"
} > "$night/summary"
rm -rf "$night/ci" && cp -r out/ci "$night/ci"
ln -sfn "$night" "$TMPDIR/lean-quiet-nightly/latest"
cat "$night/summary"
exit "$code"
