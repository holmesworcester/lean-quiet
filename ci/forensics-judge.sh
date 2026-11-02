#!/usr/bin/env bash
# The nightly forensics judge: a small Sonnet sample of two LLM indicators
# over the deterministic dump (ci/forensics.sh), with the rates appended to
# a history so they can be watched over time.
#
#   ci/forensics-judge.sh      sample, judge, append to the history
#
# Indicators: vacuity-and-misstatement (files: a law weaker than its name
# or docstring says, or vacuous) and unnecessary-hypotheses (theorems).
# The sample is the tool's seeded one, seeded by the day, so successive
# nights cover different targets; a target already judged at its current
# source is skipped. Budget: at most $THEOREMS × $0.25 + $FILES × $0.50 a
# night in per-call caps (about $1 at the measured averages, $0.025 and
# $0.117 a call). Judgments stay under .forensics/; the history is
# $FORENSICS_HISTORY/history.tsv (date, commit, indicator, flagged/judged,
# rate, 95% interval).
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/tmp}
REV=e5b80ca
tool=${FORENSICS_TOOL:-$TMPDIR/forensics-tool-$REV}
bun=${BUN:-$(command -v bun || echo /mnt/storage/bun/bin/bun)}
hist=${FORENSICS_HISTORY:-/mnt/storage/holmes-tmp/forensics-nightly}
THEOREMS=${THEOREMS:-12}
FILES=${FILES:-4}
mkdir -p "$hist"
[ -f out/forensics/model.json ] || bash ci/forensics.sh
seed=$(( $(date +%s) / 86400 ))
commit=$(git rev-parse --short HEAD)
day=$(date -u +%F)
judge() {  # indicator limit budget
  "$bun" "$tool/app/judges/run.ts" "$PWD" --from out/forensics/model.json --indicator "$1" \
    --limit "$2" --seed "$seed" --model claude-sonnet-5-5 --max-budget "$3" --jobs 2 --retries 1 \
    2> "$hist/judge-$day-$1.log" | tee -a "$hist/judge-$day-$1.log"
}
{
  judge unnecessary-hypotheses "$THEOREMS" 0.25
  judge vacuity-and-misstatement "$FILES" 0.5
} | while IFS=$'\t' read -r ind ratio rest; do
  case $ratio in */*) printf '%s\t%s\t%s\t%s\t%s\n' "$day" "$commit" "$ind" "$ratio" "$rest" >> "$hist/history.tsv" ;; esac
done
echo "forensics judge: appended to $hist/history.tsv"
tail -n 6 "$hist/history.tsv"
