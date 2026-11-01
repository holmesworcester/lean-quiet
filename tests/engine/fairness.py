#!/usr/bin/env python3
"""Run native bootstrap certificates with the vacuity gate's panic/timeout guard."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/vacuity"))
from runtime import run_checked

output = ROOT / "out/fairness"
output.mkdir(parents=True, exist_ok=True)
for name in ["vacuity_production_bootstrap",
             "vacuity_connection_progress", "vacuity_closure_delivery", "vacuity_round_exchange", "vacuity_storage_effects"]:
    print(run_checked([str(ROOT / ".lake/build/bin" / name)], ROOT,
                      output / (name + ".log"), timeout=60), end="", flush=True)
