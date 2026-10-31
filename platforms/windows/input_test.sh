#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/windows
cc -std=c11 -Wall -Wextra -Werror -fsanitize=address,undefined -g platforms/windows/input_test.c -o out/windows/input_test
out/windows/input_test
