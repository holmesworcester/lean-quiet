#!/usr/bin/env bash
# Real C transport, raw gestures, and pixel dumps of Lean's placement.
set -euo pipefail
cd "$(dirname "$0")/../.."
bash tests/app/fling.sh
lake build seam seam_app
python3 tests/app/seam.py
.lake/build/bin/seam_app
bash tests/app/layer.sh
