"""Mutate actual handlers in a scratch snapshot; require failure and restoration."""
import pathlib
import subprocess
import sys

root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)


def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=300).returncode


assert run(["lake", "build", "simplify", "syncpair", "connection_check", "Sync", "Wire"], "baseline-build") == 0
assert run([".lake/build/bin/simplify"], "baseline-run") == 0
# name, source, unique text, mutation, target, runtime assertion (None = law)
cases = [
    ("stale-terminal", "engine/sync/Conn.lean", "Decidable.decide (k < seen)", "false", "simplify", "stale terminal keeps the newer room snapshot and epoch"),
    ("round-rewind", "engine/sync/Conn.lean", "round := max c.round k", "round := k", "simplify", "older active room completes without rewinding another room"),
    ("notice-result", "engine/sync/Notice.lean", "given := x :: s.given", "given := s.given", "engine.sync.NoticeLaws", None),
    ("notice-repeat", "engine/sync/Notice.lean", "if has c.given x then", "if false then", "engine.sync.NoticeLaws", None),
    ("notice-phase", "engine/sync/Notice.lean", "{ c with given := x :: c.given }", "{ c with given := x :: c.given, session := .live }", "engine.sync.SessionLaws", None),
    ("notice-clock", "engine/sync/Notice.lean", "{ c with given := x :: c.given }", "{ c with given := x :: c.given, heard := 0 }", "engine.sync.RetryLaws", None),
    ("given-persist", "app/connection/given/Commands.lean", "def onGiven (cid x : Id) : List Op := [Given.op cid x]", "def onGiven (_cid _x : Id) : List Op := []", "connection_check", "A closes its side once the notice is given"),
    ("hello-reply", "engine/sync/Conn.lean", "{ conn := c, send := [(Msg.hello c.floor).op] }", "{ conn := c }", "engine.sync.SessionLaws", None),
    ("early-drop", "engine/sync/Conn.lean", "if c.heard + cfg.live < now then", "if c.heard + cfg.live ≤ now then", "engine.sync.TimeLaws", None),
    ("no-keepalive", "engine/sync/Conn.lean", "s.send.isEmpty && sent + cfg.live / 3 ≤ now", "false", "engine.sync.TimeLaws", None),
    ("late-keepalive", "engine/sync/Conn.lean", "s.send.isEmpty && sent + cfg.live / 3 ≤ now", "s.send.isEmpty && sent + cfg.live ≤ now", "engine.sync.TimeLaws", None),
    ("timestamp", "engine/wire/Node.lean", "then { c with sent := now } else c", "then c else c", "simplify", "node records outgoing time"),
    ("silent-room", "engine/sync/Conn.lean", "then { conn := c, send := [(Msg.rbsr r k []).op] } else", "then { conn := c } else", "engine.sync.TimeLaws", None),
    ("room-gate", "engine/sync/Conn.lean", "if c.dialer && c.lastRound + cfg.every ≤ now", "if c.dialer && c.snaps.isEmpty && c.lastRound + cfg.every ≤ now", "simplify", "a stalled room"),
    ("over-limit-handler", "engine/sync/Conn.lean", "asked := wants.foldl (·.insert ·) c.asked", "asked := (wants.foldl (·.insert ·) c.asked).insert .empty", "engine.sync.BoundsLaws", None),
    ("reopen-closed", "engine/sync/Session.lean", "def Session.hearHello : Session → Session\n  | .hello => .live\n  | s => s", "def Session.hearHello : Session → Session\n  | .closed => .live\n  | .hello => .live\n  | s => s", "engine.sync.SessionLaws", None),
    ("skip-hello", "engine/sync/Session.lean", "| .dialing => .hello", "| .dialing => .live", "engine.sync.SessionLaws", None),
    ("purge-effect", "engine/wire/Node.lean", "return { purged := ids }", "return { purged := [] }", "engine.wire.CloseLaws", None),
    ("purge-forward", "engine/wire/Node.lean", "purged := purged ++ (← Node.endSession x cid).purged", "discard <| Node.endSession x cid", "simplify", "silent peer drops and notifies purge"),
    ("purge-notify", "engine/wire/Tcp.lean", "unless e.purged.isEmpty do notify e.purged", "unless e.purged.isEmpty do pure ()", "simplify", "TCP apply notifies purges"),
    ("stream-secret", "engine/sync/Conn.lean", "if c.shows fam o then\n          offer :=", "if true then\n          offer :=", "engine.sync.SecrecyLaws", None),
    ("closure-secret", "engine/sync/Conn.lean", "if c.shows fam o then\n          let offer :=", "if true then\n          let offer :=", "engine.sync.SecrecyLaws", None),
    ("stream-absent", "engine/sync/Conn.lean", "| none => pure ()\n  return { conn := c, send := holdsOf", "| none => offer := (c.rooms.headD .empty, i) :: offer\n  return { conn := c, send := holdsOf", "engine.sync.SecrecyLaws", None),
    ("closure-absent", "engine/sync/Conn.lean", "| none => c.walkN offer budget", "| none => c.walkN ((c.rooms.headD .empty, x) :: offer) budget", "engine.sync.SecrecyLaws", None),
    ("completion", "engine/sync/Conn.lean", "take := [o]", "take := []", "engine.wire.WorldLaws", None),
]
for name, source, old, mutant, target, expected in cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, mutant))
        code = run(["lake", "build", target], name + "-build")
        if expected:
            assert code == 0, (name, "runtime mutant must compile")
            exe = "connection_check" if name == "given-persist" else "simplify"
            code = run([".lake/build/bin/" + exe], name)
            result = (logs / (name + ".log")).read_text()
        else:
            result = (logs / (name + "-build.log")).read_text()
            expected = "error:"
        assert code != 0 and expected in result, (name, "survived or failed elsewhere")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0, (name, "restoration")
assert run(["lake", "build", "simplify", "Sync", "Wire"], "restored-build") == 0
assert run([".lake/build/bin/simplify"], "restored-run") == 0
print(f"simplify negative controls: {len(cases)} refused; restored suite passes")
