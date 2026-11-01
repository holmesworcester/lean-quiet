#!/usr/bin/env bash
# Render a manifest's cases with the real renderer, several processes at
# once: each case has its own database and files, so the cases split
# across VISUAL_JOBS processes (8 by default) give the same pictures.
#   tests/visual/capture.sh <out-dir> <cases.tsv>
set -euo pipefail
cd "$(dirname "$0")/../.."
dir=$1 manifest=$2 jobs=${VISUAL_JOBS:-8}
mkdir -p "$dir"
parts=$(mktemp -d "${TMPDIR:-/tmp}/visual-cases.XXXXXX")
trap 'rm -rf -- "$parts"' EXIT
grep -v '^#' "$manifest" | grep . > "$parts/all" || true
[ -s "$parts/all" ] || { echo "no cases in $manifest" >&2; exit 1; }
split -n "r/$jobs" -d "$parts/all" "$parts/part."
pids=() files=()
for p in "$parts"/part.*; do
  [ -s "$p" ] || continue
  case $p in *.log) continue ;; esac
  .lake/build/bin/visual "$dir" "$p" > "$p.log" 2>&1 & pids+=($!) files+=("$p")
done
fail=0
for i in "${!pids[@]}"; do
  code=0; wait "${pids[$i]}" || code=$?
  if [ "$code" != 0 ]; then
    fail=1
    echo "visual capture: part $i of $manifest exited $code; its cases and log:" >&2
    sed 's/^/  case: /' "${files[$i]}" >&2
    sed 's/^/  log: /' "${files[$i]}.log" >&2
  fi
done
cat "$parts"/part.*.log
[ "$fail" = 0 ] || { echo "visual capture failed for $manifest" >&2; exit 1; }
echo "captured $(wc -l < "$parts/all") cases from $manifest"
