#!/usr/bin/env bash
# Prerequisites: Linux/ELF GNU-compatible linker, C compiler, Lean toolchain,
# and the Rust archive built by the named Mise task's crypto dependency.
# All build output and failure diagnostics remain under out/crypto-failure.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
output=out/crypto-failure
mkdir -p "$output"
include=$(lean --print-prefix)/include
# These two Rust tests query the actual locked cipher's remaining-block API.
# The boundary is measured without allocating the 256 GiB input it describes.
CARGO_TARGET_DIR="$PWD/engine/native/crypto/target" cargo test --release --locked \
  --manifest-path engine/native/crypto/Cargo.toml
cc -O2 -std=gnu11 -Wall -Wextra -Werror -I"$include" -c tests/engine/crypto_failure.c -o "$output/test.o"
cc -O2 -std=gnu11 -I"$include" -c engine/native/crypto.c -o "$output/crypto.o"
leanc "$output/test.o" "$output/crypto.o" engine/native/crypto/target/release/liblq_crypto.a \
  -Wl,--wrap=lq_chachapoly_seal -Wl,--wrap=lq_xchacha_seal \
  -pthread -ldl -lm -lrt \
  -o "$output/check"
"$output/check" 2>&1 | tee "$output/check.log"
