#!/usr/bin/env bash
# The nightly forensics judge, on current main, in its own worktree
# ($NIGHTLY_TREE, default /mnt/storage/holmes-wt/lq-nightly, detached at
# origin/main; created on first run). Started by the systemd user timer
# ci/nightly/lq-forensics-judge.timer (install: ci/nightly/install.sh).
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && git rev-parse --git-common-dir)
tree=${NIGHTLY_TREE:-/mnt/storage/holmes-wt/lq-nightly}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan} TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export PATH="$ELAN_HOME/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git --git-dir="$repo" fetch -q origin
[ -d "$tree" ] || git --git-dir="$repo" worktree add -q --detach "$tree" origin/main
cd "$tree"
git checkout -q --detach origin/main
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build >/dev/null
rm -f out/forensics/model.json
bash ci/forensics.sh
bash ci/forensics-judge.sh
