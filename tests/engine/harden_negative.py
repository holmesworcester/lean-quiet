"""Execute Daybreak negative controls in an isolated, restored snapshot."""
import pathlib, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)

def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=300).returncode

assert run(["lake", "build", "harden", "ops.sync.TimeLaws", "ops.sync.BoundsLaws", "ops.sync.RetryLaws", "ops.sync.ServeLaws", "engine.wire.CloseLaws", "engine.wire.Slots"], "baseline-build") == 0
assert run([".lake/build/bin/harden"], "baseline-run") == 0
# (name, source, unique original, mutant, target, expected failure text, runtime?)
cases = [
    ("wait-origin", "ops/sync/Conn.lean", "def Conn.waitStart (c : Conn) : Nat := max c.heard c.lastRound", "def Conn.waitStart (c : Conn) : Nat := c.heard", "ops.sync.TimeLaws", "round_not_dropped", False),
    ("no-lease", "ops/sync/Conn.lean", " || c.expired cfg now then", " then", "ops.sync.TimeLaws", "error:", False),
    ("early-lease", "ops/sync/Conn.lean", "!c.dialer && c.heard + cfg.lease < now", "!c.dialer && c.heard < now", "ops.sync.TimeLaws", "error:", False),
    ("uncarried-room", "ops/sync/Conn.lean", "  if !has c.rooms r then { conn := c } else", "  if !has c.rooms r || c.snaps.isEmpty then { conn := c } else", "ops.sync.TimeLaws", "error:", False),
    ("no-purge", "engine/wire/Node.lean", "  if !ids.isEmpty then Turn.purge x.fam ids true", "  if !ids.isEmpty then pure ()", "engine.wire.CloseLaws", "error:", False),
    ("no-close-event", "engine/wire/Node.lean", "  n.finish x { drop := ids } now", "  n.finish x {} now", "harden", "transport end", True),
    ("known-forget", "ops/sync/Memory.lean", "then next else ({} : HashSet Id).insert i", "then next else next", "ops.sync.RetryLaws", "error:", False),
    ("asked-admission", "ops/sync/Memory.lean", "if s.size < cap then s.insert i else s", "s.insert i", "ops.sync.BoundsLaws", "error:", False),
    ("size-drop", "ops/sync/Conn.lean", "conn := { s.conn with known := {}, asked := {}, stale := {} } }", "conn := { s.conn with known := {}, asked := {}, stale := {} }, drop := true }", "ops.sync.RetryLaws", "error:", False),
    ("no-expiry", "ops/sync/Conn.lean", "let c := c.age cfg now", "let c := c", "harden", "asks expire", True),
    ("expiry-law", "ops/sync/Conn.lean", "{ c with stale := c.asked, asked := {}, askedAt := now }", "{ c with askedAt := now }", "ops.sync.RetryLaws", "error:", False),
    ("defer-asks", "ops/sync/Memory.lean", "(ids.filter fun i => !asked.contains i && !stale.contains i).eraseDups", "((ids.filter fun i => !asked.contains i && !stale.contains i).eraseDups).take 1", "ops.sync.RetryLaws", "error:", False),
    ("unlimited-sets", "ops/sync/Conn.lean", "if s.conn.known.size ≤ cfg.maxKnown ∧ s.conn.asked.size ≤ cfg.maxKnown then s", "if True then s", "ops.sync.BoundsLaws", "error:", False),
    ("oversized-hold", "ops/sync/Conn.lean", "  if ids.length > cfg.maxIds then return { conn := c }\n  let mut want", "  if False then return { conn := c }\n  let mut want", "harden", "oversized hold", True),
    ("unauthorized-read", "ops/sync/Conn.lean", "ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)", "ids", "harden", "never reads large x", True),
    ("blindness", "ops/sync/Conn.lean", "ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)", "ids", "ops.sync.ServeLaws", "error:", False),
    ("no-budget", "ops/sync/Serve.lean", "else (serve shows (budget - o.bytes.size) ids).map fun p => (o :: p.1, p.2)", "else (serve shows budget ids).map fun p => (o :: p.1, p.2)", "ops.sync.ServeLaws", "error:", False),
    ("no-budget-stop", "ops/sync/Serve.lean", "if budget ≤ o.bytes.size then .done ([o], ids)\n          else (serve shows (budget - o.bytes.size) ids).map fun p => (o :: p.1, p.2)", "(serve shows budget ids).map fun p => (o :: p.1, p.2)", "harden", "budget stops", True),
    ("unbounded-queue", "engine/wire/Tcp.lean", "Std.CloseableChannel.Sync.new (some cfg.queue)", "Std.CloseableChannel.Sync.new none", "harden", "full queue blocks producer", True),
    ("dropping-queue", "engine/wire/Tcp.lean", "return (← (ch.send ev).toBaseIO).isOk", "return (← ch.trySend ev)", "harden", "blocked frame delivered", True),
    ("no-socket-cap", "engine/wire/Slots.lean", "if admit cfg peers peer then", "if true then", "harden", "socket cap", True),
    ("admission-law", "engine/wire/Slots.lean", "peers.length < cfg.maxSocks && (peers.filter (· == peer)).length < cfg.perAddr", "true", "engine.wire.Slots", "error:", False),
    ("close-effects", "engine/wire/Tcp.lean", "r.1.apply x ch notify cfg r.2 now", "r.1.apply x ch notify cfg { r.2 with send := [] } now", "harden", "close effects", True),
    ("shared-socket", "engine/wire/Tcp.lean", "unless st.node.conns.any fun (c, _) => st.node.addr? c == some addr do", "unless false do", "harden", "shared socket: a dropped session leaves the socket up", True),
    ("v6-one-quota", "engine/wire/Slots.lean", "  match String.fromUTF8? addr with\n  | none => \"?\"\n  | some s =>\n    if s.startsWith \"[\" then (s.splitOn \"]\").headD s ++ \"]\"\n    else match s.splitOn \":\" with\n      | [host, _] => host\n      | _ => s\n", "  ((String.fromUTF8! addr).splitOn \":\").headD \"?\"\n", "harden", "IPv6 peers have separate quotas", True),
    ("v6-placeholder", "engine/wire/Tcp.lean", "| .v6 a => s!\"[{a.addr}]:{a.port}\"", "| .v6 a => s!\"[v6]:{a.port}\"", "harden", "an IPv6 address's text names its host", True),
]
for name, source, old, new, target, expected, runtime in cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, new))
        code = run(["lake", "build", target], name + "-build")
        if runtime:
            assert code == 0, (name, "mutant must compile before runtime control")
            code = run([".lake/build/bin/harden"], name)
            text = (logs / (name + ".log")).read_text()
        else:
            text = (logs / (name + "-build.log")).read_text()
        # Lean errors may report a source line rather than the theorem name.
        needle = "error:" if expected == "round_not_dropped" else expected
        assert code != 0 and needle in text, (name, "survived or failed for a different reason")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0, (name, "restored source did not build")
assert run(["lake", "build", "harden"], "restored-build") == 0
assert run([".lake/build/bin/harden"], "restored-run") == 0
print(f"harden negative controls: {len(cases)} refused; restored suite passes")
