"""Execute Daybreak negative controls: the snapshot built and passing,
then each mutant in a copy of its own, HARDEN_NC_JOBS (6) at once."""
import concurrent.futures, os, pathlib, shutil, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)

def run(args, name, cwd=root):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=cwd, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode

assert run(["lake", "build", "harden", "engine.sync.TimeLaws", "engine.sync.BoundsLaws", "engine.sync.RetryLaws", "engine.sync.ServeLaws", "engine.wire.CloseLaws", "engine.wire.Slots"], "baseline-build") == 0
assert run([".lake/build/bin/harden"], "baseline-run") == 0
# (name, source, unique original, mutant, target, expected failure text, runtime?)
cases = [
    ("uncarried-room", "engine/sync/Conn.lean", "  if !has c.carried r then { conn := c, send := [(Msg.rbsr r k []).op] } else", "  if !has c.carried r || c.active.isEmpty then { conn := c, send := [(Msg.rbsr r k []).op] } else", "engine.sync.TimeLaws", "error: engine/sync/TimeLaws.lean", False),
    ("no-purge", "engine/wire/Node.lean", "  if !ids.isEmpty then Turn.purge x.fam ids scrub", "  if !ids.isEmpty then pure ()", "engine.wire.CloseLaws", "error:", False),
    ("no-close-event", "engine/wire/Node.lean", "  n.finish x { drop := ids } now", "  n.finish x {} now", "harden", "transport end", True),
    ("known-forget", "engine/sync/Memory.lean", "then next else ({} : HashSet Id).insert i", "then next else next", "engine.sync.RetryLaws", "error:", False),
    ("asked-admission", "engine/sync/Memory.lean", ".take (cap - asked.size)", "", "harden", "full asked defers", True),
    ("no-expiry", "engine/sync/Conn.lean", "let c := c.expireAsks cfg now", "let c := c", "harden", "asks expire", True),
    ("expiry-law", "engine/sync/Conn.lean", "asked := c.asked.filter live", "asked := c.asked.filter (fun _ => true)", "engine.sync.RetryLaws", "error: engine/sync/RetryLaws.lean", False),
    ("offer-renews", "engine/sync/Conn.lean", "askTime := accepted.foldl (fun ts i => ts.insert i c.heard) c.askTime", "askTime := accepted.foldl (fun ts i => ts.insert i c.heard) (c.askTime.map (fun _ _ => c.heard))", "harden", "repeat offers do not renew", True),
    ("retry-renews", "engine/sync/Conn.lean", "lastAsk := if due then now else c.lastAsk }", "lastAsk := if due then now else c.lastAsk, askTime := c.askTime.map (fun _ _ => now) }", "harden", "retries do not renew", True),
    ("retry-cap", "engine/sync/Conn.lean", "c.asked.toList.take cfg.maxIds", "c.asked.toList", "engine.sync.RetryLaws", "error:", False),
    ("oversized-hold", "engine/sync/Conn.lean", "  if ids.length > cfg.maxIds then return { conn := c }\n  let mut want", "  if False then return { conn := c }\n  let mut want", "harden", "oversized hold", True),
    ("unauthorized-read", "engine/sync/Conn.lean", "ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)", "ids", "harden", "never reads large x", True),
    ("blindness", "engine/sync/Conn.lean", "ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)", "ids", "engine.sync.ServeLaws", "error:", False),
    ("no-budget", "engine/sync/Serve.lean", "else (serve shows (budget - o.bytes.size) ids).map fun p => (o :: p.1, p.2)", "else (serve shows budget ids).map fun p => (o :: p.1, p.2)", "engine.sync.ServeLaws", "error:", False),
    ("no-budget-stop", "engine/sync/Serve.lean", "if budget ≤ o.bytes.size then .done ([o], ids)\n          else (serve shows (budget - o.bytes.size) ids).map fun p => (o :: p.1, p.2)", "(serve shows budget ids).map fun p => (o :: p.1, p.2)", "harden", "budget stops", True),
    ("unbounded-queue", "engine/wire/Tcp.lean", "def eventChannel (cfg : RunConfig) : IO (Std.CloseableChannel.Sync Event) :=\n  Std.CloseableChannel.Sync.new (some cfg.queue)", "def eventChannel (cfg : RunConfig) : IO (Std.CloseableChannel.Sync Event) :=\n  Std.CloseableChannel.Sync.new none", "harden", "full queue blocks producer", True),
    ("dropping-queue", "engine/wire/Tcp.lean", "  repeat\n    if (← cancel) || (← ch.isClosed) then return false\n    if ← ch.trySend ev then return true\n    IO.sleep 1", "  return (← ch.trySend ev)", "harden", "blocked frame delivered", True),
    ("no-socket-cap", "engine/wire/Slots.lean", "if admit cfg peers peer then", "if true then", "harden", "socket cap", True),
    ("admission-law", "engine/wire/Slots.lean", "peers.length < cfg.maxSocks && (peers.filter (· == peer)).length < cfg.perAddr", "true", "engine.wire.Slots", "error:", False),
    ("close-effects", "engine/wire/Tcp.lean", "r.1.apply x ch notify cfg r.2 now", "r.1.apply x ch notify cfg { r.2 with send := [] } now", "harden", "close effects", True),
    ("no-retry", "engine/sync/Conn.lean", "chunks cfg (c.retryIds cfg now) .want", "chunks cfg [] .want", "harden", "tick reasks", True),
    ("shared-socket", "engine/wire/Tcp.lean", "unless st.node.conns.any fun (c, _) => st.node.addr? c == some addr do", "unless false do", "harden", "shared socket: a dropped session leaves the socket up", True),
    ("v6-one-quota", "engine/wire/Slots.lean", "  match String.fromUTF8? addr with\n  | none => \"?\"\n  | some s =>\n    if s.startsWith \"[\" then (s.splitOn \"]\").headD s ++ \"]\"\n    else match s.splitOn \":\" with\n      | [host, _] => host\n      | _ => s\n", "  ((String.fromUTF8! addr).splitOn \":\").headD \"?\"\n", "harden", "IPv6 peers have separate quotas", True),
    ("v6-placeholder", "engine/wire/Tcp.lean", "| .v6 a => s!\"[{a.addr}]:{a.port}\"", "| .v6 a => s!\"[v6]:{a.port}\"", "harden", "an IPv6 address's text names its host", True),
]
def control(case):
    name, source, old, new, target, expected, runtime = case
    work = root.parent / ("mutant-" + name)
    shutil.copytree(root, work, symlinks=True)
    try:
        path = work / source
        original = path.read_text()
        assert original.count(old) == 1, (name, "mutation target missing")
        path.write_text(original.replace(old, new))
        code = run(["lake", "build", target], name + "-build", work)
        if runtime:
            assert code == 0, (name, "mutant must compile before runtime control")
            code = run([str(work / ".lake/build/bin/harden")], name, work)
            text = (logs / (name + ".log")).read_text()
        else:
            text = (logs / (name + "-build.log")).read_text()
        assert code != 0 and expected in text, (name, "survived or failed for a different reason")
        return name
    finally:
        shutil.rmtree(work)

with concurrent.futures.ThreadPoolExecutor(int(os.environ.get("HARDEN_NC_JOBS", "6"))) as pool:
    for name in pool.map(control, cases):
        print("refused:", name, flush=True)
print(f"harden negative controls: {len(cases)} refused, each in its own copy")
