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
    ("uncarried-room", "ops/sync/Conn.lean", "  if !has c.rooms r then { conn := c, send := [(Msg.rbsr r k []).op] } else", "  if !has c.rooms r || c.snaps.isEmpty then { conn := c, send := [(Msg.rbsr r k []).op] } else", "ops.sync.TimeLaws", "error:", False),
    ("no-purge", "engine/wire/Node.lean", "  if !ids.isEmpty then Turn.purge x.fam ids scrub", "  if !ids.isEmpty then pure ()", "engine.wire.CloseLaws", "error:", False),
    ("no-close-event", "engine/wire/Node.lean", "  n.finish x { drop := ids } now", "  n.finish x {} now", "harden", "transport end", True),
    ("known-forget", "ops/sync/Memory.lean", "then next else ({} : HashSet Id).insert i", "then next else next", "ops.sync.RetryLaws", "error:", False),
    ("asked-admission", "ops/sync/Memory.lean", ".take (cap - asked.size)", "", "harden", "full asked defers", True),
    ("no-expiry", "ops/sync/Conn.lean", "let c := c.expireAsks cfg now", "let c := c", "harden", "asks expire", True),
    ("expiry-law", "ops/sync/Conn.lean", "asked := c.asked.filter live", "asked := c.asked.filter (fun _ => true)", "ops.sync.RetryLaws", "error: ops/sync/RetryLaws.lean", False),
    ("offer-renews", "ops/sync/Conn.lean", "askTime := accepted.foldl (fun ts i => ts.insert i c.heard) c.askTime", "askTime := accepted.foldl (fun ts i => ts.insert i c.heard) (c.askTime.map (fun _ _ => c.heard))", "harden", "repeat offers do not renew", True),
    ("retry-renews", "ops/sync/Conn.lean", "lastAsk := if due then now else c.lastAsk }", "lastAsk := if due then now else c.lastAsk, askTime := c.askTime.map (fun _ _ => now) }", "harden", "retries do not renew", True),
    ("retry-cap", "ops/sync/Conn.lean", "c.asked.toList.take cfg.maxIds", "c.asked.toList", "ops.sync.RetryLaws", "error:", False),
    ("oversized-hold", "ops/sync/Conn.lean", "  if ids.length > cfg.maxIds then return { conn := c }\n  let mut want", "  if False then return { conn := c }\n  let mut want", "harden", "oversized hold", True),
    ("unauthorized-read", "ops/sync/Conn.lean", "ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)", "ids", "harden", "never reads large x", True),
    ("blindness", "ops/sync/Conn.lean", "ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)", "ids", "ops.sync.ServeLaws", "error:", False),
    ("no-budget", "ops/sync/Serve.lean", "else (serve shows (budget - o.bytes.size) ids).map (o :: ·)", "else (serve shows budget ids).map (o :: ·)", "ops.sync.ServeLaws", "error:", False),
    ("no-budget-stop", "ops/sync/Serve.lean", "if budget ≤ o.bytes.size then .done [o]\n          else (serve shows (budget - o.bytes.size) ids).map (o :: ·)", "(serve shows budget ids).map (o :: ·)", "harden", "budget stops", True),
    ("unbounded-queue", "engine/wire/Tcp.lean", "Std.CloseableChannel.Sync.new (some cfg.queue)", "Std.CloseableChannel.Sync.new none", "harden", "full queue blocks producer", True),
    ("dropping-queue", "engine/wire/Tcp.lean", "return (← (ch.send ev).toBaseIO).isOk", "return (← ch.trySend ev)", "harden", "blocked frame delivered", True),
    ("no-socket-cap", "engine/wire/Slots.lean", "if admit cfg peers peer then", "if true then", "harden", "socket cap", True),
    ("admission-law", "engine/wire/Slots.lean", "peers.length < cfg.maxSocks && (peers.filter (· == peer)).length < cfg.perAddr", "true", "engine.wire.Slots", "error:", False),
    ("close-effects", "engine/wire/Tcp.lean", "r.1.apply x ch notify cfg r.2 now", "r.1.apply x ch notify cfg { r.2 with send := [] } now", "harden", "close effects", True),
    ("no-retry", "ops/sync/Conn.lean", "chunks cfg (c.retryIds cfg now) .want", "chunks cfg [] .want", "harden", "tick reasks", True),
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
        assert code != 0 and expected in text, (name, "survived or failed for a different reason")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0, (name, "restored source did not build")
assert run(["lake", "build", "harden"], "restored-build") == 0
assert run([".lake/build/bin/harden"], "restored-run") == 0
print(f"harden negative controls: {len(cases)} refused; restored suite passes")
