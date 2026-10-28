#!/usr/bin/env bash
set -euo pipefail
top=$(cd "$(dirname "$0")/../.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
cd "$top"
mkdir -p out/linux
cc -std=gnu11 -O1 -g -Wall -Wextra -Werror -ffunction-sections -fdata-sections \
  -fsanitize=address,undefined -I "$(lean --print-prefix)/include" \
  platforms/linux/input_test.c -Wl,--gc-sections -lxcb -lxcb-shm -o out/linux/input_test
# LeakSanitizer cannot inspect processes under this sandbox's ptrace
# restrictions. ASan's memory checks and UBSan remain enabled.
ASAN_OPTIONS=detect_leaks=0 out/linux/input_test
