#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p out/photo
cc -std=c11 -g -Wall -Wextra -Werror -fsanitize=address,undefined -pthread platforms/native/photo_test.c -o out/photo/native-test
ASAN_OPTIONS=detect_leaks=0 out/photo/native-test
