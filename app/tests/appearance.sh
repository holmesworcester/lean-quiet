#!/usr/bin/env bash
# Real process restart and live OS reporting on the headless app.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
lake build appearance appearance_seam
out=out/appearance
mkdir -p "$out"
case ${1:-all} in
  restart|all)
    for setting in system light dark; do
      .lake/build/bin/appearance write "$out/restart-$setting" "$setting"
      .lake/build/bin/appearance read "$out/restart-$setting" "$setting"
    done
    ;;
esac
case ${1:-all} in
  live|all) .lake/build/bin/appearance live "$out"; python3 tests/theme-palette.py; tests/theme-seam.sh ;;
esac
