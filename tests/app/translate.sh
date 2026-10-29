#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build translate
python3 tests/app/translate.py
