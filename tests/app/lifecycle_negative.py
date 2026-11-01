#!/usr/bin/env python3
"""Reversible mutants of running code. Never edits tests or proof statements."""
from pathlib import Path
import os
import subprocess
import sys
sys.dont_write_bytecode = True
from lifecycle_env import network_env

root = Path(__file__).resolve().parents[2]
out = root / "out/app-lifecycle/negative"
out.mkdir(parents=True, exist_ok=True)
env = network_env()
env["ELAN_HOME"] = "/mnt/storage/elan"
env["PATH"] = "/mnt/storage/elan/bin:" + env["PATH"]
env["TMPDIR"] = "/mnt/storage/holmes-tmp"
# name, file, before, after, executable (None means the proof must fail)
mutants = [
    ("allow-unmounted", "app/Screen.lean", "m.mounted && decide (l.generation = m.generation)", "true", None),
    ("deny-mounted-witness", "app/Screen.lean", "m.mounted && decide (l.generation = m.generation)", "false", None),
    ("ignore-lease", "app/Screen.lean", "if s.allows l then some <$> action else pure none", "some <$> action", None),
    ("lose-subscriptions", "app/Screen.lean", "m.queries.map fun q => (q.win default).key", "[]", None),
    ("retain-unmounted-cache", "app/Screen.lean", "l.keep fun q => s.queries.contains q", "l", None),
    ("shift-anchor", "app/Screen.lean", "top - above", "top - above + 1", None),
    ("lose-checkpoint", "app/Screen.lean", "Option Checkpoint := Codec.decode bytes", "Option Checkpoint := none", None),
    ("wrong-page-tag", "app/Screen.lean", "| 0 => .home | 1 => .chat", "| 0 => .home | 1 => .home", None),
    ("read-after-unmount", "app/Screen.lean", "  if !s.life.allows s.life.lease then return default\n", "", None),
    ("write-after-unmount", "app/Screen.lean", "  if !s.life.allows s.life.lease then return false\n", "", None),
    ("run-old-callback", "app/Screen.lean", "Lifecycle.owned (← get).life l action", "some <$> action", None),
    ("save-wrong-page", "app/Screen.lean", "(1, s.page.code, s.cur, a.1, a.2,", "(1, 0, s.cur, a.1, a.2,", None),
    ("apply-wrong-anchor", "app/Screen.lean", "mark := if x.isEmpty then none else some (x, off)", "mark := none", None),
    ("wrong-placement", "engine/renderer/Geometry.lean", "(g.top : Int) - over + r + ((bn : Int) - bf) - g.shift", "(g.top : Int) - over + r + ((bn : Int) - bf) - g.shift + 1", None),
    ("no-fitting-viewport", "engine/renderer/Geometry.lean", "def Geom.Fits (g : Geom) : Prop := g.top + g.bot + max g.insetBot g.ime ≤ g.h", "def Geom.Fits (g : Geom) : Prop := False", None),
    ("keep-old-layout", "app/Screen.lean", "let lay := Row.layout s.font dm w r.data", "let lay := r.lay", "suite"),
    ("draw-without-surface", "app/Screen.lean", "if !s.active || !s.surface || s.netStop.isSome then\n      IO.sleep 16", "if false then\n      IO.sleep 16", "suite"),
    ("lose-camera-teardown", "app/Screen.lean", "if s.camOn then s.io.scan false", "if false then s.io.scan false", "suite"),
    ("lose-write-journal", "app/Screen.lean", "queuedWrites := s.queuedWrites ++ j.ops.map Op.bytes", "queuedWrites := s.queuedWrites", "crash"),
    ("lose-native-draft", "app/Screen.lean", 's.io.setText t', 's.io.setText ""', "suite"),
    ("lose-os-links", "app/Screen.lean", " ++ (← io.links).toList.map Event.deepLink", "", "suite"),
    ("lose-resize-keyboard", "app/Screen.lean", "if s.active && s.surface && s.life.mounted && inputPage == (s.page, s.cur) then", "if false then", "suite"),
    ("stale-home-count", "app/Screen.lean", "people := ms.size, ", "", "two"),
    ("truncate-dump-path", "platforms/headless/host.c", "dump(line + 6);", "dump(strndup(line + 6, 63));", "twin"),
    ("drop-parked-writes", "app/Screen.lean", "net := none, netBoot := none, restoreAnchor := s.mark.isSome", "net := none, netBoot := none, toNode := #[], restoreAnchor := s.mark.isSome", "suite"),
    ("lose-reader-barrier", "app/Screen.lean", "  stopReader\n  retirePaints s", "  retirePaints s", "suite"),
    ("retain-picture-wants", "app/Screen.lean", "picWants := #[], retryWants := {}, lastSlices := none }", "picWants := s.picWants, retryWants := s.retryWants, lastSlices := s.lastSlices }", "suite"),
    ("lose-producer-writes", "app/Screen.lean", "toNode := s.toNode ++ jobs.map (·.ops)", "toNode := s.toNode", "suite"),
    ("retain-listener", "engine/wire/Tcp.lean", "  closeListener r.listener\n", "", "restart"),
    ("reverse-parked-order", "app/Screen.lean", "toNode := s.toNode.push j.ops", "toNode := #[j.ops] ++ s.toNode", "suite"),
    ("retain-reader-cache", "app/Screen.lean", "live := s.live.keep held.contains", "live := s.live", "suite"),
    ("lose-anchor-fallback", "app/Screen.lean", "else if s.restoreAnchor then", "else if false then", "suite"),
    ("ignore-unchanged-window", "app/Screen.lean", " || s.restoreAnchor then some (ids, newer, older, total)", " then some (ids, newer, older, total)", "suite"),
    ("forget-pending-anchor", "app/Screen.lean", "mark := if s.restoreAnchor then s.mark else captureAnchor s", "mark := captureAnchor s", "suite"),
    ("lose-last-native-edit", "app/Screen.lean", "  captureInput\n", "", "suite"),
]

def run(cmd, log, timeout=300):
    code = subprocess.run(cmd, cwd=root, env=env, stdout=log,
                          stderr=subprocess.STDOUT, timeout=timeout).returncode
    log.flush()
    output = Path(log.name).read_text()
    assert code not in (137, -9) and "code: 137" not in output and "Killed" not in output, "build killed: inspect memory use; not a negative-control result"
    return code

start = int(os.environ.get("LIFECYCLE_NEGATIVE_START", "0"))
selected = set(filter(None, os.environ.get("LIFECYCLE_NEGATIVE_NAMES", "").split(",")))
ran = 0
for name, file, before, after, executable in mutants[start:]:
    if selected and name not in selected:
        continue
    path = root / file
    original = path.read_bytes()
    text = original.decode()
    assert text.count(before) == 1, (name, text.count(before))
    try:
        path.write_text(text.replace(before, after))
        with (out / (name + ".log")).open("w") as log:
            target = {"two": "two_nodes", "twin": "twin_demo", "restart": "runner_restart"}.get(executable,
                "app_lifecycle" if executable else "app.Proofs")
            code = run(["lake", "build", target], log)
            if executable:
                assert code == 0, name + ": mutation failed to build; no runtime result"
                if executable == "restart":
                    code = run([str(root / ".lake/build/bin/runner_restart"), "--local"], log)
                elif executable == "crash":
                    code = run(["python3", "tests/app/lifecycle.py", "out/app-lifecycle/mutant"], log)
                elif executable == "two":
                    code = run([str(root / ".lake/build/bin/two_nodes"), "out/app-lifecycle/mutant-two"], log)
                elif executable == "twin":
                    code = run(["tests/app/host_twin_demo.sh", str(out / "long-screenshot-path-negative-control")], log)
                else:
                    code = run([str(root / ".lake/build/bin/app_lifecycle"), "out/app-lifecycle/mutant"], log)
            assert code != 0, name + ": negative control unexpectedly passed"
        print("rejected " + name, flush=True)
        ran += 1
    finally:
        path.write_bytes(original)
# Rebuild pristine code; a failed control never leaves a mutant on disk.
with (out / "restored.log").open("w") as log:
    assert run(["lake", "build", "app_lifecycle", "quiet_host"], log) == 0
print(f"{ran} negative controls rejected; source restored", flush=True)
