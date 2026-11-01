#!/usr/bin/env python3
"""Resume regressions: build each mutant, require its specific failure,
restore the source, and rebuild the production entry point at the end."""
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[2]
out = root / "out/lifecycle-node/negative"
out.mkdir(parents=True, exist_ok=True)
# name, file, original, mutant, expected assertion/error, wiring check?
cases = [
    ("home-count", "app/Screen.lean", "  refreshHomeCount\n", "", "Home's count follows", False),
    ("no-deadline", "app/Screen.lean", "    if (← IO.monoMsNow) + 5 ≥ deadline then return false", "    if false then return false", "suspend returns within its deadline", False),
    ("drop-stop", "app/Screen.lean", "netStop := some stopping", "netStop := none", "timed-out runner remains owned", False),
    ("leave-late-boot", "app/Screen.lean", "if let .ok r ← IO.wait t then r.stop", "discard <| IO.wait t", "a runner born after timeout is stopped", False),
    ("read-after-revoke", "app/Screen.lean", "  if !(← s.enabled) then return default\n", "", "revoked reader issues no query", False),
    ("publish-after-revoke", "app/Screen.lean", "      unless (← enabled) && (← sh.current ticket) do", "      unless (← sh.current ticket) do", "revoked pass cannot publish", False),
    # Both retained lifecycle owners protect this case; bypass the complete unsafe-offer guard.
    ("offer-while-stopping", "app/Screen.lean", "if !s.active || !s.surface || s.net.isSome || s.netBoot.isSome || s.netStop.isSome || s.netReplay.isSome then", "if !s.active || !s.surface || s.net.isSome || s.netBoot.isSome then", "foreground writes also park", False),
    ("join-unfinished-stop", "app/Screen.lean", "if let some t := s.netStop then\n    if ← IO.hasFinished t then", "if let some t := s.netStop then\n    if true then", "suspend returns within its deadline", False),
    ("drop-reader", "app/Screen.lean", "readerStop := s.reader.orElse fun _ => s.readerStop", "readerStop := none", "timed-out work remains owned", False),
    ("drop-completed-act", "app/Screen.lean", "  parkDone s.sh\n", "", "suspend parks and checkpoints a completed reader act", False),
    ("accept-revoked-act", "app/Screen.lean", "          if !(← (← get).enabled) then pure none\n          else pure (some (w, ← judgeWrite rd (← get).out w))", "          pure (some (w, ← judgeWrite rd (← get).out w))", "an intent revoked in flight produces no write", False),
    ("desktop-anchor", "platforms/desktop/Driver.lean", "  let (_, s) ← (App.resize (← d.screen.get)).run d.app", "  let s := if d.app.W == aw && d.app.Hs == ah then d.app else { d.app with W := aw, Hs := ah, bgRow := Paint.solid Row.bg aw, rows := {}, heights := {}, imgs := {}, pageKey := none, chromeKey := \"\", gridKey := \"\", gridRows := {} }", "desktop resize preserves the message anchor", "desktop"),
    ("missing-exemption", "tests/wiring.txt", "bounded App.suspend One shared 250ms deadline via waitFor; unfinished teardown remains owned, and resume only polls it.\n", "", "block: the frame waits on App.waitFor", True),
    ("broad-exemption", "tests/wiring.txt", "bounded App.suspend One shared", "bounded App.resumeReader invalid exemption\nbounded App.suspend One shared", "bounded: only the reached App.suspend", True),
    ("blocking-resume", "app/Screen.lean", "def resumeReader : M Unit := do\n", "def resumeReader : M Unit := do\n  discard <| IO.wait (Task.pure ())\n", "block: the frame waits on IO.wait", True),
    ("synchronous-replay", "app/Screen.lean", "    let replay ← IO.asTask (prio := .dedicated)\n      (replayStoppedNodeWrites s.netBoot s.net s.wr s.queuedWrites)\n", "    replayStoppedNodeWrites s.netBoot s.net s.wr s.queuedWrites\n    let replay ← IO.asTask (prio := .dedicated) (pure ())\n", "bounded: App.suspend reaches unbounded IO.wait", True),
    ("unbounded-suspend", "app/Screen.lean", "def suspend (budget : Nat := 250) : M Unit := do\n", "def suspend (budget : Nat := 250) : M Unit := do\n  discard <| IO.wait (Task.pure ())\n", "bounded: App.suspend reaches unbounded IO.wait", True),
    ("commit-on-frame", "app/Screen.lean", "  s.wr.save (Codec.encode cp)\n", "  Lifecycle.save (← openDb s.dbPath) (Codec.encode cp)\n", "a frame during a purge's checkpoint returns at once", False),
    ("commit-on-frame-wiring", "app/Screen.lean", "  s.wr.save (Codec.encode cp)\n", "  Lifecycle.save (← openDb s.dbPath) (Codec.encode cp)\n", "block: the frame waits on Lifecycle.save", True),
    ("checkpoint-failure-loses-job", "app/Commands.lean", "      w.jobs.modify (·.push j)\n", "      w.busy.modify (· - 1)\n", "a failed checkpoint keeps its following job pending", False),
]

def run(cmd, path):
    with path.open("w") as log:
        child = subprocess.Popen(cmd, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        path.with_suffix(".pid").write_text(str(child.pid) + "\n")
        try:
            code = child.wait(timeout=300)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait()
            raise
    text = path.read_text()
    assert code not in (137, -9) and "code: 137" not in text and "Killed" not in text, "memory-cap failure, not a negative control"
    return code, text

selected = os.environ.get("LIFECYCLE_NODE_CONTROLS", "").split(",")
ran = 0
for name, file, old, new, expected, wiring in cases:
    if selected != [""] and name not in selected:
        continue
    path = root / file
    original = path.read_bytes()
    text = original.decode()
    assert text.count(old) == 1, (name, "mutation target missing")
    try:
        mutant = text.replace(old, new)
        if name == "accept-revoked-act":
            guard = "        if !(← (← get).enabled) then break\n"
            assert mutant.count(guard) == 1
            mutant = mutant.replace(guard, "")
        path.write_text(mutant)
        code, _ = run(["lake", "build", "desktop" if wiring == "desktop" else "app_lifecycle_node", "+Main"], out / (name + "-build.log"))
        assert code == 0, (name, "mutant must build")
        cmd = [".lake/build/bin/desktop", "out/lifecycle-node/desktop-mutant"] if wiring == "desktop" else ["lake", "env", "lean", "--run", "tests/Wiring.lean"] if wiring else [".lake/build/bin/app_lifecycle_node", "out/lifecycle-node/mutant"]
        code, text = run(cmd, out / (name + ".log"))
        assert code != 0 and expected in text, (name, "wrong failure or surviving mutant")
        print("rejected " + name, flush=True)
        ran += 1
    finally:
        path.write_bytes(original)
assert run(["lake", "build", "app_lifecycle_node", "quiet_host", "desktop", "+Main"], out / "restored-build.log")[0] == 0
assert run([".lake/build/bin/app_lifecycle_node", "out/lifecycle-node/restored"], out / "restored-run.log")[0] == 0
print(f"lifecycle node controls: {ran} rejected; source restored; positive suite passes", flush=True)
