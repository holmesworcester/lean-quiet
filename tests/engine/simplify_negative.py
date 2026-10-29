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
    ("notice-result", "ops/sync/Notice.lean", "given := x :: s.given", "given := s.given", "ops.sync.NoticeLaws", None),
    ("notice-repeat", "ops/sync/Notice.lean", "if has c.given x then", "if false then", "ops.sync.NoticeLaws", None),
    ("notice-phase", "ops/sync/Notice.lean", "{ c with given := x :: c.given }", "{ c with given := x :: c.given, session := .live }", "ops.sync.SessionLaws", None),
    ("notice-clock", "ops/sync/Notice.lean", "{ c with given := x :: c.given }", "{ c with given := x :: c.given, heard := 0 }", "ops.sync.RetryLaws", None),
    ("given-persist", "ops/connection/Intents.lean", "def onGiven (cid x : Id) : List Op := [Given.op cid x]", "def onGiven (_cid _x : Id) : List Op := []", "connection_check", "A closes its side once the notice is given"),
    ("hello-reply", "ops/sync/Conn.lean", "{ conn := c, send := [(Msg.hello c.floor).op] }", "{ conn := c }", "ops.sync.SessionLaws", None),
    ("early-drop", "ops/sync/Conn.lean", "if c.heard + cfg.live < now then", "if c.heard + cfg.live ≤ now then", "ops.sync.TimeLaws", None),
    ("no-keepalive", "ops/sync/Conn.lean", "s.send.isEmpty && sent + cfg.live / 3 ≤ now", "false", "ops.sync.TimeLaws", None),
    ("late-keepalive", "ops/sync/Conn.lean", "s.send.isEmpty && sent + cfg.live / 3 ≤ now", "s.send.isEmpty && sent + cfg.live ≤ now", "ops.sync.TimeLaws", None),
    ("timestamp", "engine/wire/Node.lean", "then { c with sent := now } else c", "then c else c", "simplify", "node records outgoing time"),
    ("silent-room", "ops/sync/Conn.lean", "then { conn := c, send := [(Msg.rbsr r k []).op] } else", "then { conn := c } else", "ops.sync.TimeLaws", None),
    ("room-gate", "ops/sync/Conn.lean", "if c.dialer && c.lastRound + cfg.every ≤ now", "if c.dialer && c.snaps.isEmpty && c.lastRound + cfg.every ≤ now", "simplify", "a stalled room"),
    ("over-limit-handler", "ops/sync/Conn.lean", "asked := wants.foldl (·.insert ·) c.asked", "asked := (wants.foldl (·.insert ·) c.asked).insert .empty", "ops.sync.BoundsLaws", None),
    ("reopen-closed", "ops/sync/Session.lean", "def Session.hearHello : Session → Session\n  | .hello => .live\n  | s => s", "def Session.hearHello : Session → Session\n  | .closed => .live\n  | .hello => .live\n  | s => s", "ops.sync.SessionLaws", None),
    ("skip-hello", "ops/sync/Session.lean", "| .dialing => .hello", "| .dialing => .live", "ops.sync.SessionLaws", None),
    ("purge-effect", "engine/wire/Node.lean", "return { purged := ids }", "return { purged := [] }", "engine.wire.CloseLaws", None),
    ("purge-forward", "engine/wire/Node.lean", "purged := purged ++ (← Node.endSession x cid).purged", "discard <| Node.endSession x cid", "simplify", "silent peer drops and notifies purge"),
    ("purge-notify", "engine/wire/Tcp.lean", "unless e.purged.isEmpty do notify e.purged", "unless e.purged.isEmpty do pure ()", "simplify", "TCP apply notifies purges"),
    ("stream-secret", "ops/sync/Conn.lean", "if c.shows fam o then\n          offer :=", "if true then\n          offer :=", "ops.sync.SecrecyLaws", None),
    ("closure-secret", "ops/sync/Conn.lean", "if c.shows fam o then\n          let offer :=", "if true then\n          let offer :=", "ops.sync.SecrecyLaws", None),
    ("stream-absent", "ops/sync/Conn.lean", "| none => pure ()\n  return { conn := c, send := holdsOf", "| none => offer := (c.rooms.headD .empty, i) :: offer\n  return { conn := c, send := holdsOf", "ops.sync.SecrecyLaws", None),
    ("closure-absent", "ops/sync/Conn.lean", "| none => c.walkN offer budget", "| none => c.walkN ((c.rooms.headD .empty, x) :: offer) budget", "ops.sync.SecrecyLaws", None),
    ("completion", "ops/sync/Conn.lean", "take := [o]", "take := []", "engine.wire.WorldLaws", None),
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
