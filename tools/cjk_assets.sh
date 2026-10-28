#!/bin/sh
# Offline, reproducible common CJK assets. Full font inputs are never shipped.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$root/assets"
if (cd "$root/assets" && sha256sum -c "$root/tools/cjk-subsets.sha256" --status) 2>/dev/null; then exit 0; fi
export PYTHONPATH="${CJK_PYTHON:-/mnt/storage/holmes-wt/lq-tonight/py}${PYTHONPATH:+:$PYTHONPATH}"
python3 "$root/tools/cjk_subset.py" --fonts "${CJK_FONTS:-/mnt/storage/holmes-wt/lq-tonight/fonts}"
(cd "$root/assets" && sha256sum -c "$root/tools/cjk-subsets.sha256")
