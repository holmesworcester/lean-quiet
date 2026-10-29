"""Report actual frame/coverage samples; reject lost typing/blank recovery
in Scrolling.lean, and sustained placeholder backlog here. Timing is an
observation, not a wall-clock theorem. Keep CSV alongside the report."""
import argparse
import csv
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument("csv", type=Path)
p.add_argument("--check", action="store_true")
a = p.parse_args()
rows = list(csv.DictReader(a.csv.open()))
fling = [r for r in rows if r["phase"] == "fling"]
times = sorted(int(r["step_us"]) for r in fling)
report = {
    "frames": len(fling),
    "frame_ms_median": times[len(times) // 2] / 1000,
    "frame_ms_p95": times[int(len(times) * .95)] / 1000,
    "frame_ms_max": max(times) / 1000,
    "frames_with_placeholders": sum(int(r["missing_pixels"]) > 0 for r in fling),
    "placeholder_pixel_frames": sum(int(r["missing_pixels"]) for r in fling),
    "worst_missing_pixels": max(int(r["missing_pixels"]) for r in fling),
    "stop_frames_until_painted": sum(r["phase"] == "stop" for r in rows),
}
a.csv.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
if a.check:
    # Allow cold rows to fill; fail if the pool backlog blanks most of the
    # fling. The baseline under the same injected backlog is a control.
    assert report["frames_with_placeholders"] < len(fling) // 2, report
    assert report["stop_frames_until_painted"] <= 100, report
