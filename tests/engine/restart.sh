#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build runner_restart
if [ "${SKIP_TCP:-0}" = 1 ]; then
  .lake/build/bin/runner_restart --local
  echo 'SKIP same-port TCP restart (sandbox; executable built)'
else
  .lake/build/bin/runner_restart
fi
