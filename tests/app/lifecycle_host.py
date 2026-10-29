#!/usr/bin/env python3
"""Production Main + host.c: events must arrive even without a frame."""
from pathlib import Path
import os
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
out = (root / (sys.argv[1] if len(sys.argv) > 1 else "out/app-lifecycle")).resolve() / "seam"
out.mkdir(parents=True, exist_ok=True)
assets = out / "assets"
if not assets.exists():
    assets.symlink_to(root / "assets", target_is_directory=True)
for suffix in ["", "-wal", "-shm"]:
    (out / ("quiet.db" + suffix)).unlink(missing_ok=True)
script = out / "events.txt"
script.write_text("""found Seam|Ann
!sync
channel
!text seam draft
!ime 300
!background
!surface 0
!frames 3
!foreground
!frames 2
!resize 960 720
!surface 1
!frames 2
state
!ime 0
!resize 480 1000
!frames 2
state
!background
!surface 0
!frames 2
!surface 1
!foreground
!frames 2
state
open invite
link
""")
env = dict(os.environ, QUIET_SCRIPT=str(script))
result = subprocess.run([str(root / ".lake/build/bin/quiet_host")], cwd=out,
                        env=env, text=True, capture_output=True, timeout=60)
(out / "stdout.log").write_text(result.stdout)
(out / "stderr.log").write_text(result.stderr)
assert result.returncode == 0, result.stderr
states = [line for line in result.stdout.splitlines() if line.startswith("b ")]
assert len(states) == 3, result.stdout
assert all('text "seam draft"' in line for line in states), states
assert all("ime 0" in line for line in states), states
# The C twin aborts on any frame without an active surface. Continuing
# through both suspensions also proves poll works without calling frame.
print("lifecycle C twin: 3 state checks, 2 suspensions, 2 resizes passed")

link = next(line for line in result.stdout.splitlines() if line.startswith("quiet://join/"))
link_dir = out / "link"
link_dir.mkdir(exist_ok=True)
if not (link_dir / "assets").exists():
    (link_dir / "assets").symlink_to(root / "assets", target_is_directory=True)
for suffix in ["", "-wal", "-shm"]:
    (link_dir / ("quiet.db" + suffix)).unlink(missing_ok=True)
link_script = link_dir / "events.txt"
link_script.write_text("invite\n!link " + link + "\n!frames 1\ninvite\n")
result = subprocess.run([str(root / ".lake/build/bin/quiet_host")], cwd=link_dir,
    env=dict(os.environ, QUIET_SCRIPT=str(link_script), QUIET_LINK=link),
    text=True, capture_output=True, timeout=30)
(link_dir / "stdout.log").write_text(result.stdout)
(link_dir / "stderr.log").write_text(result.stderr)
assert result.returncode == 0, result.stderr
assert result.stdout.splitlines().count(link) == 2, result.stdout
print("lifecycle C twin: cold and warm invite delivery passed")
