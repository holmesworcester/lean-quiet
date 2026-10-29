#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build engine.renderer.SlideLaws +engine.renderer.Slide:c
python3 tests/app/slide.py
