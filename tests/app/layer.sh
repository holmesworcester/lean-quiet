#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p out/seam
lake build +engine.renderer.Slide:c +engine.renderer.Translate:c +engine.renderer.Surface:c +engine.renderer.Geometry:c +engine.renderer.Cover:c >/dev/null
include=$(lean --print-prefix)/include
cc -O2 -std=gnu11 -I"$include" -pthread -c tests/app/layer.c -o out/seam/layer.o
objects=()
for module in Slide Translate Surface Geometry Cover; do
  cc -O2 -std=gnu11 -I"$include" -c ".lake/build/ir/engine/renderer/$module.c" -o "out/seam/$module.o"
  objects+=("out/seam/$module.o")
done
lake env leanc -pthread out/seam/layer.o "${objects[@]}" -o out/seam/layer
out/seam/layer
