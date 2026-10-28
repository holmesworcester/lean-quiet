#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
bash build.sh
bash input_test.sh
mkdir -p ../../out/linux
cc -std=gnu11 -O1 -Wall -Wextra -Werror sync_test.c -lxcb -lxcb-sync -o ../../out/linux/sync_test
python3 test.py
