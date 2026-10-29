#!/usr/bin/env bash
# Explicit reference refresh, isolated from the application comparison gate.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export PLAYWRIGHT_BROWSERS_PATH="$PWD/out/visual/browsers"
export PYTHONPATH="$PWD/out/visual/python${PYTHONPATH:+:$PYTHONPATH}"
mkdir -p out/visual/python
python3 -m pip install --quiet --target out/visual/python --upgrade 'playwright==1.58.0'
if [ -z "${CHROME:-}" ]; then python3 -m playwright install chromium; fi
python3 tests/visual/capture_reference.py "$@"
