#!/usr/bin/env bash
# Offline, non-RELEASE: both the ref twin and the C seam's event pump.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ -f assets/font.bin ] || { echo 'local app assets are required' >&2; exit 1; }
lake build app_lifecycle quiet_host
python3 tests/app/lifecycle.py "${1:-out/app-lifecycle}"
python3 tests/app/lifecycle_host.py "${1:-out/app-lifecycle}"
