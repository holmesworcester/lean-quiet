#!/usr/bin/env bash
# The proofslop forensics tool's deterministic pass (no LLM): build, the
# extractor (axioms, statement smells, flags per declaration), Lean's
# linters, duplicate statements; then ci/forensics_check.py fails on a
# smell outside ci/forensics-baseline.txt (which may only shrink) and on
# any nonstandard axiom, sorry, native_decide or kernel escape hatch.
#
#   ci/forensics.sh            run it, writing out/forensics/model.json
#
# The tool is for-all-dev/forensics at a pinned commit, with this repo's
# patches (ci/forensics-local.patch: lint job count, logged lint failures,
# Lean core under $ELAN_HOME, a retries flag), prepared once under
# $TMPDIR/forensics-tool ($FORENSICS_TOOL to use a local clone instead).
# Needs bun (1.4.4 or later: $BUN, on PATH, or /mnt/storage/bun/bin/bun).
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/tmp}
REV=e5b80ca
tool=${FORENSICS_TOOL:-$TMPDIR/forensics-tool-$REV}
bun=${BUN:-$(command -v bun || echo /mnt/storage/bun/bin/bun)}
[ -x "$bun" ] || { echo "forensics: no bun (set BUN, or install bun 1.4.4+)" >&2; exit 1; }
if [ ! -d "$tool/app" ]; then
  git clone -q https://github.com/for-all-dev/forensics.git "$tool"
  git -C "$tool" checkout -q "$REV"
  git -C "$tool" apply "$PWD/ci/forensics-local.patch"
  (cd "$tool/app" && "$bun" install --silent)
fi
# The extractor and duplicates checker build once per toolchain, here,
# not under ~/.cache.
export XDG_CACHE_HOME="$TMPDIR/forensics-cache"
export FORENSICS_LINT_JOBS=${FORENSICS_LINT_JOBS:-8}
# the roots: every library module, the app, and the vacuity witnesses
# (not their *Main wrappers, which each declare `main`)
roots=$( { find engine app platforms/desktop -name '*.lean'; echo Quiet.lean;
           find tests/vacuity -name '*.lean' ! -name '*Main.lean'; } |
         sed 's/\.lean$//; s#/#.#g' | sort | paste -sd, -)
mkdir -p out/forensics
"$bun" "$tool/app/server.ts" "$PWD" --roots "$roots" --dump out/forensics/model.json
python3 ci/forensics_check.py out/forensics/model.json
