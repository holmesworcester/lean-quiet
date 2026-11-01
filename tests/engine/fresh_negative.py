"""Negative controls of the send lanes (docs/SYNC.md, "Lanes"), in an
isolated snapshot: each mutant must fail its law, or the TCP test. A
mutant's `old` and `new` may be tuples: edits to one file together."""
import pathlib, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)

def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode

assert run(["lake", "build", "engine.wire.LaneLaws", "engine.sync.ServeLaws", "engine.wire.WorldLaws", "fresh_tcp"], "baseline-build") == 0
assert run([".lake/build/bin/fresh_tcp"], "baseline-run") == 0
# Control the actual acceptor's scheduling in this scratch snapshot only.
# The gate uses this runner's completed tick counter, not an elapsed delay:
# the fixed fixture leaves established empty until admission, while the old
# ordering publishes during those ticks and dials S's non-listening port.
tcp = root / "engine/wire/Tcp.lean"
fixture = root / "tests/engine/FreshTcp.lean"
tcp_before, fixture_before = tcp.read_text(), fixture.read_text()
startup_changes = [
    ("(cfg : RunConfig) : IO Unit := do\n  repeat\n    if ← stopped.get then return",
     "(cfg : RunConfig) (beforeAdmit : IO Unit := pure ()) : IO Unit := do\n  repeat\n    if ← stopped.get then return"),
    ("      if ← slots.take cfg peer.toUTF8 then\n        unless ← enqueue ch (.accepted c peer.toUTF8) stopped.get do",
     "      if ← slots.take cfg peer.toUTF8 then\n        beforeAdmit\n        unless ← enqueue ch (.accepted c peer.toUTF8) stopped.get do"),
    ("  let listening ← IO.asTask (prio := .dedicated) (acceptor ch srv stopped slots cfg)\n  let turnCounters ← IO.mkRef ({} : TurnCounters)",
     "  let turnCounters ← IO.mkRef ({} : TurnCounters)\n  let beforeAdmit : IO Unit := do\n    let before := (← turnCounters.get).ticks.toNat\n    while (← turnCounters.get).ticks.toNat < before + 2 && !(← stopped.get) do IO.sleep 1\n  let listening ← IO.asTask (prio := .dedicated) (acceptor ch srv stopped slots cfg beforeAdmit)"),
]
try:
    gated = tcp_before
    for old, new in startup_changes:
        assert gated.count(old) == 1, ("startup scheduling gate", "missing unique anchor")
        gated = gated.replace(old, new)
    tcp.write_text(gated)
    assert run(["lake", "build", "fresh_tcp"], "startup-gated-build") == 0
    assert run([".lake/build/bin/fresh_tcp"], "startup-gated-positive") == 0
    old = "  let admitted ← waitFor 2000 do return (← rr.lanes).any (·.1 == sAddr.toUTF8)"
    assert fixture_before.count(old) == 1, "startup control missing admission barrier"
    fixture.write_text(fixture_before.replace(old, "  let admitted := true"))
    assert run(["lake", "build", "fresh_tcp"], "startup-old-order-build") == 0, "old ordering must compile"
    code = run([".lake/build/bin/fresh_tcp"], "startup-old-order")
    result = (logs / "startup-old-order.log").read_text()
    assert code == 1 and "FAIL: S is not closed before stallMs" in result, "wrong startup-order failure"
    assert not any(marker in result.lower() for marker in
                   ["panic", "segmentation fault", "assertion violation", "uncaught exception", "network runner stopped:"]), "invalid startup-order failure"
    print("refused: startup-before-admission (two completed runner ticks)", flush=True)
finally:
    tcp.write_text(tcp_before)
    fixture.write_text(fixture_before)

# (name, source, unique original, mutant, target, expected failure text, runtime?)
cases = [
    ("discard-retired", "engine/wire/Tcp.lean",
     "    if drain then s.drain else s.stop", "    s.stop",
     "fresh_tcp", "FAIL: retired final notice arrives first, before ordinary backlog and EOF", True),
    ("event-starves-write", "engine/wire/Lanes.lean",
     "  let selected ← if writeFirst then do",
     "  let selected ← if false then do",
     "engine.wire.LaneLaws", "error:", False),
    ("one-lane", "engine/wire/Lanes.lean",
     "  | .urgent, f => { q with urgent := q.urgent ++ [f] }",
     "  | .urgent, f => { q with serve := q.serve ++ [f] }",
     "engine.wire.LaneLaws", "error:", False),
    ("no-burst-cap", "engine/wire/Lanes.lean",
     "    let (a, b) := fill (burst - f.size) fs\n    (f :: a, b)",
     "    (f :: fs, [])",
     "engine.wire.LaneLaws", "error:", False),
    ("no-hot", "engine/wire/Node.lean",
     "  n.hot.filterMap fun p => if now ≤ p.2 + x.cfg.hotMs then some p.1 else none",
     "  if now ≤ x.cfg.hotMs then [] else []",
     "engine.wire.LaneLaws", "error:", False),
    ("hot-last", "engine/sync/Conn.lean",
     "def Conn.hotOf (c : Conn) (first : List Id) : List Id := (first.filter c.owing.contains).eraseDups.take 1",
     "def Conn.hotOf (c : Conn) (first : List Id) : List Id := []",
     "fresh_tcp", "FAIL: a fresh write wanted is served urgent, whatever the budget", True),
    ("truncated-want", "engine/sync/Conn.lean",
     ".eraseDups.take (cfg.maxKnown - c.owed.length)",
     ".eraseDups.take 1",
     "engine.sync.ServeLaws", "error:", False),
    ("want-jumps-queue", "engine/sync/Conn.lean",
     "{ conn := { c with owed := c.owed ++ add, owing := add.foldl (·.insert ·) c.owing } }",
     "{ conn := { c with owed := add ++ c.owed, owing := add.foldl (·.insert ·) c.owing } }",
     "engine.sync.ServeLaws", "error:", False),
    ("cold-write", "engine/wire/Node.lean",
     "  (n.heat x n.fresh now).finish x out now",
     "  n.finish x out now",
     "engine.wire.WorldLaws", "error:", False),
    ("no-cap", "engine/wire/Lanes.lean",
     "  if q'.bytes ≤ cap then some q' else none",
     "  some q'",
     "engine.wire.LaneLaws", "error:", False),
    ("stall-blind", "engine/wire/Lanes.lean",
     "  heard + idle < now || since.any (· + stallMs ≤ now)",
     "  heard + idle < now",
     "engine.wire.LaneLaws", "error:", False),
    ("blocking-send", "engine/wire/Tcp.lean",
     "      unless ordinary.isEmpty do discard <| s.push cfg ordinary",
     "      for (_, b) in ordinary do discard <| sendOn s.client b",
     "fresh_tcp", "FAIL: P gets all 64 ops while S never reads", True),
    # The frame handler serves with no room (each frame its `burst`).
    ("no-room", "engine/wire/Tcp.lean",
     "      let (st, e) ← st.node? fun n => n.step x' (.frame s.addr p) now",
     "      let (st, e) ← st.node? fun n => n.step x (.frame s.addr p) now",
     "fresh_tcp", "FAIL: S's lanes stay within the window", True),
    # The room is blind to what the lanes hold (`Sock.queued := 0`).
    ("room-blind", "engine/wire/Tcp.lean",
     "  let qs ← socks.mapM fun s => do return (s.addr, ← s.lanes)",
     "  let qs ← socks.mapM fun s => do return (s.addr, ({} : Lanes))",
     "fresh_tcp", "FAIL: S's lanes stay within the window", True),
    # Both the loop and the native writer must inherit the disabled deadline.
    ("no-timeout", "engine/wire/Tcp.lean",
     "    IO Runner := do\n  let x :=",
     "    IO Runner := do\n  let cfg := { cfg with stallMs := 86400000 }\n  let x :=",
     "fresh_tcp", "FAIL: S is closed within stallMs", True),
    # The slot is released at close, while the writer still waits.
    ("slot-at-close", "engine/wire/Tcp.lean",
     ("  finally\n    cleanupReader\n    slots.release addr", "    if drain then s.drain else s.stop\n    return ({ st.drop sid with\n      node\n      sessionGrace := st.sessionGrace.filter fun (cid, _) => node.conns.any (·.1 == cid) }, e)"),
     ("  finally\n    cleanupReader\n    pure ()", "    if drain then s.drain else s.stop\n    st.slots.release s.addr\n    return ({ st.drop sid with\n      node\n      sessionGrace := st.sessionGrace.filter fun (cid, _) => node.conns.any (·.1 == cid) }, e)"),
     "fresh_tcp", "FAIL: actual native writer holds its lease before deadline (closed=false, retired=true)", True),
]
if sys.platform != "win32":
    cases.extend([
        ("no-native-abort", "engine/wire/SocketAbort.lean",
         "        unless ← cap.abort do", "        unless true do",
         "fresh_tcp", "FAIL: never-reading peer cannot retain writer or slot after deadline (closed=false, retired=false)", True),
        ("early-send-return", "engine/wire/SocketAbort.lean",
         "  let .ok promise ← operation.toBaseIO | return false",
         "  let .ok promise ← operation.toBaseIO | return false\n  if true then return false",
         "fresh_tcp", "FAIL: actual native writer holds its lease before deadline (closed=false, retired=false)", True),
    ])
for name, source, old, new, target, expected, runtime in cases:
    path = root / source
    original = path.read_text()
    olds, news = (old, new) if isinstance(old, tuple) else ((old,), (new,))
    mutant = original
    for o, n in zip(olds, news):
        assert mutant.count(o) == 1, (name, "mutation target missing", o)
        mutant = mutant.replace(o, n)
    try:
        path.write_text(mutant)
        code = run(["lake", "build", target], name + "-build")
        if runtime:
            assert code == 0, (name, "mutant must compile before runtime control")
            code = run([".lake/build/bin/" + target], name)
            text = (logs / (name + ".log")).read_text()
            assert code > 0, (name, "native control must report a test failure, not terminate by a signal")
            assert not any(marker in text.lower() for marker in
                ["panic", "segmentation fault", "assertion violation", "uncaught exception", "network runner stopped:"]), \
                (name, "native failure is not a valid negative-control result")
        else:
            text = (logs / (name + "-build.log")).read_text()
            assert "error: " + target.replace(".", "/") + ".lean" in text, \
                (name, "must be rejected by the unchanged target proof, not an unrelated dependency")
        assert code != 0 and expected in text, (name, "survived or failed for a different reason")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0, (name, "restored source did not build")
assert run(["lake", "build", "engine.wire.LaneLaws", "engine.sync.ServeLaws", "engine.wire.WorldLaws", "fresh_tcp"], "restored-build") == 0
assert run([".lake/build/bin/fresh_tcp"], "restored-run") == 0
print(f"fresh negative controls: {len(cases) + 1} refused; restored suite passes")
