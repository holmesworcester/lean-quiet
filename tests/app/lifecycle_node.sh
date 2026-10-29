#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build app_lifecycle_node
.lake/build/bin/app_lifecycle_node "${1:-out/lifecycle-node}"
