#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
bash build.sh
bash input_test.sh
python3 test.py
