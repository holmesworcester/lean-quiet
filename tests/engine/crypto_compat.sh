#!/usr/bin/env bash
# The Rust crypto against libsodium, byte for byte (tests/crypto_compat.c).
set -euo pipefail
cd "$(dirname "$0")/.."
(cd native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
mkdir -p out
cc -O2 -o out/crypto_compat tests/crypto_compat.c native/crypto/target/release/liblq_crypto.a \
  /usr/lib/x86_64-linux-gnu/libsodium.so.23 -lpthread -ldl -lm -lrt
out/crypto_compat
