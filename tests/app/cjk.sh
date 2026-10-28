#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export PYTHONPATH="${CJK_PYTHON:-/mnt/storage/holmes-wt/lq-tonight/py}${PYTHONPATH:+:$PYTHONPATH}"
tools/noto_assets.sh
python3 tests/app/cjk_reference.py prepare
lake build cjk cjk_scroll
.lake/build/bin/cjk out/cjk
python3 tests/app/cjk_reference.py compare
.lake/build/bin/cjk_scroll out/cjk-after out/cjk/corpus.txt
