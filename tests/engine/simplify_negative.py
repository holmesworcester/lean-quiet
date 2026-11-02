"""Mutate actual handlers, each mutant in a copy of its own of a scratch
snapshot (tests/mutants.py); require each to fail."""
import pathlib
import subprocess
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import mutants

root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)


def run(args, name, cwd=root):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=cwd, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode


assert run(["lake", "build", "simplify", "live_rounds", "syncpair", "connection_check", "Sync", "Wire"], "baseline-build") == 0
assert run([".lake/build/bin/simplify"], "baseline-run") == 0
assert run([".lake/build/bin/live_rounds"], "baseline-live-run") == 0
# name, source, unique text, mutation, target, runtime assertion (None = law)
cases = [
    ("stale-terminal", "engine/sync/Conn.lean", "Decidable.decide (k < seen)", "false", "simplify", "stale terminal keeps the newer room round and epoch"),
    ("round-rewind", "engine/sync/Conn.lean", "round := max c.round k", "round := k", "simplify", "older active room completes without rewinding another room"),
    ("notice-result", "engine/sync/Notice.lean", "given := x :: s.given", "given := s.given", "engine.sync.NoticeLaws", None),
    ("notice-repeat", "engine/sync/Notice.lean", "if has c.given x then", "if false then", "engine.sync.NoticeLaws", None),
    ("notice-phase", "engine/sync/Notice.lean", "{ c with given := x :: c.given }", "{ c with given := x :: c.given, session := .live }", "engine.sync.SessionLaws", None),
    ("notice-clock", "engine/sync/Notice.lean", "{ c with given := x :: c.given }", "{ c with given := x :: c.given, heard := 0 }", "engine.sync.RetryLaws", None),
    ("given-persist", "app/connection/given/Commands.lean", "def onGiven (cid x : Id) : List Op := [Given.op cid x]", "def onGiven (_cid _x : Id) : List Op := []", "connection_check", "A closes its side once the notice is given"),
    ("hello-reply", "engine/sync/Conn.lean", "{ conn := { c with rounded := c.carried.map (·, now) }, send := [(Msg.hello c.floor).op] }", "{ conn := { c with rounded := c.carried.map (·, now) } }", "engine.sync.SessionLaws", None),
    ("early-drop", "engine/sync/Conn.lean", "if c.heard + cfg.live < now then", "if c.heard + cfg.live ≤ now then", "engine.sync.TimeLaws", None),
    ("no-keepalive", "engine/sync/Conn.lean", "s.send.isEmpty && sent + cfg.live / 3 ≤ now", "false", "engine.sync.TimeLaws", None),
    ("late-keepalive", "engine/sync/Conn.lean", "s.send.isEmpty && sent + cfg.live / 3 ≤ now", "s.send.isEmpty && sent + cfg.live ≤ now", "engine.sync.TimeLaws", None),
    ("timestamp", "engine/wire/Node.lean", "then { c with sent := now } else c", "then c else c", "simplify", "node records outgoing time"),
    ("silent-room", "engine/sync/Conn.lean", "then { conn := c, send := [(Msg.rbsr r k []).op] } else", "then { conn := c } else", "engine.sync.TimeLaws", None),
    ("room-gate", "engine/sync/Conn.lean", "let ready := c.carried.filter fun r => c.due cfg r now", "let ready := c.carried.filter fun r => c.active.isEmpty && c.due cfg r now", "simplify", "a stalled room does not gate it"),
    ("no-show-round", "engine/sync/Conn.lean", "  | none => true\n  | some t => Decidable.decide (t + cfg.safety ≤ now)", "  | none => false\n  | some t => Decidable.decide (t + cfg.safety ≤ now)", "simplify", "showing a room starts a round"),
    ("cadence", "engine/sync/Conn.lean", "  | some t => Decidable.decide (t + cfg.safety ≤ now)", "  | some t => Decidable.decide (t + cfg.safety ≤ now) || true", "simplify", "with no event, no round starts before the safety period"),
    ("no-safety", "engine/sync/Conn.lean", "  | some t => Decidable.decide (t + cfg.safety ≤ now)", "  | some t => Decidable.decide (t + cfg.safety ≤ now) && false", "simplify", "the safety round reopens each room"),
    ("responder-silent", "engine/sync/Conn.lean", "  let s := if c.dialer then c.start cfg ix now else c.ask cfg now", "  let s := if c.dialer then c.start cfg ix now else { conn := c }", "simplify", "the responder asks for a round"),
    ("ask-ignored", "engine/sync/Conn.lean", "      if ids.isEmpty then return { conn := c.onAsk r }", "      if ids.isEmpty then return { conn := c }", "simplify", "a responder's ask opens a round"),
    # main's rounds as shipped (b4d103a): the dialer rounds on its own timer only, the responder never asks.
    ("main-cadence", "engine/sync/Conn.lean", "  let s := if c.dialer then c.start cfg ix now else c.ask cfg now", "  let s := if c.dialer && c.rounded.isEmpty then c.start cfg ix now else { conn := c }", "live_rounds", "joining responder: its ask opens a round"),
    ("join-no-show", "engine/sync/Conn.lean", "    rounded := (c.rounded.filter fun p => has rooms p.1 && has c.rooms p.1 || has takes p.1 && has c.takes p.1).take all.length", "    rounded := (c.rounded.filter fun p => true).take all.length", "engine.sync.EventLaws", None),
    ("hub-snapshot", "engine/sync/Conn.lean", "  let c := if claims.isEmpty then ended c else { c with active := ((r, k) :: others).take c.carried.length }", "  let c := if claims.isEmpty then ended c else { c with active := ((r, k) :: others).take c.carried.length, given := (ix.items r).map (·.2) ++ c.given }", "live_rounds", "hub mid-round: no per-round copy of the room"),
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
def control(case, work):
    name, source, old, mutant, target, expected = case
    path = work / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    path.write_text(original.replace(old, mutant))
    code = run(["lake", "build", target], name + "-build", work)
    if expected:
        assert code == 0, (name, "runtime mutant must compile")
        exe = "connection_check" if name == "given-persist" else ("live_rounds" if target == "live_rounds" else "simplify")
        code = run([str(work / ".lake/build/bin" / exe)], name, work)
        result = (logs / (name + ".log")).read_text()
    else:
        result = (logs / (name + "-build.log")).read_text()
        expected = "error:"
    assert code != 0 and expected in result, (name, "survived or failed elsewhere")
    return "refused: " + name


mutants.each(root, cases, control)
print(f"simplify negative controls: {len(cases)} refused, each in its own copy")
