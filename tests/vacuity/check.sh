#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mise run test:crypto-failure
python3 tests/vacuity/audit.py
python3 tests/vacuity/controls.py
python3 tests/vacuity/inventory_test.py
python3 tests/vacuity/runner_test.py
python3 ci/vacuity.py
