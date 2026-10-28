"""The n-node World's negative controls (engine/world), each run on a
scratch snapshot, never the working sources.

Each control mutates the running code, and every closed form or law of
holmes-a3's or the engine's that would refuse it first is stubbed, so
the build reaches the World law the control is about; the control passes
only if the build then fails inside that law (an error line between the
theorem's first line and the next declaration). A control that builds,
or fails anywhere else, fails the gate. The snapshot is restored after
each control, and the restored targets must build."""
import pathlib, re, subprocess, sys

root, logs = map(pathlib.Path, sys.argv[1:3])
only = sys.argv[3:]
logs.mkdir(parents=True, exist_ok=True)

def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=3600).returncode

def stub(name):
    """Replace theorem `name`'s proof with `sorry` (a stub for a law that
    would refuse the mutant before the World law does)."""
    return ("stub", name)

def span(text, thm):
    """Theorem `thm`'s lines, 1-based: its first line, and the next
    declaration's (exclusive)."""
    lines = text.split("\n")
    pat = re.compile(r"^(@\[[^\]]*\] )?(theorem|lemma) " + re.escape(thm) + r"\s")
    start = next(i for i, l in enumerate(lines) if pat.match(l + " "))
    end = next((i for i in range(start + 1, len(lines))
                if re.match(r"^(@\[|theorem |lemma |def |abbrev |structure |/--|section|end|variable|omit|include|/-!)", lines[i])),
               len(lines))
    return start + 1, end + 1

def apply_stub(text, thm):
    """`thm`'s tactic proof replaced by `sorry`."""
    lines = text.split("\n")
    s, e = span(text, thm)
    i = s - 1
    while i < e - 1 and ":= by" not in lines[i]:
        i += 1
    assert ":= by" in lines[i], (thm, "no tactic proof to stub")
    head = lines[i][: lines[i].index(":= by") + len(":= by")]
    return "\n".join(lines[:i] + [head, "  sorry", ""] + lines[e - 1:])

# (name, edits, target module, World file, World theorem)
# An edit is (file, old, new) for the running code or a closed form that
# follows it, or (file, stub(theorem)).
cases = [
    ("filed-drops-a-have",
     [("ops/sync/Conn.lean", "  return Conn.finish { conn := c, send := holdsOf cfg offer.reverse }",
       "  return Conn.finish { conn := c, send := holdsOf cfg (offer.reverse.drop 1) }"),
      ("ops/sync/OfferLaws.lean", stub("filed_keeps")),
      ("engine/world/Stream.lean", "(holdsOf cfg (ids.foldl (fileStep' fam h.db) ([], c)).1.reverse) [] [] false), h) := by",
       "(holdsOf cfg ((ids.foldl (fileStep' fam h.db) ([], c)).1.reverse.drop 1)) [] [] false), h) := by")],
     "engine.world.Stream", "engine/world/Stream.lean", "filed_offers'"),
    ("want-ignores-room",
     [("ops/sync/Conn.lean", "  let sent ← (serve (c.shows fam) cfg.wantBytes (authorize ix c ids)).run (Store.getOp (F := F))",
       "  let sent ← (serve (fun o => c.shows fam o || true) cfg.wantBytes (authorize ix c ids)).run (Store.getOp (F := F))"),
      ("ops/sync/ServeLaws.lean", stub("want_blind_step")),
      ("ops/sync/ServeLaws.lean", stub("onWant_one")),
      ("ops/sync/ServeLaws.lean", stub("want_budget")),
      ("ops/sync/ConnLaws.lean", stub("onWant_send")),
      ("ops/sync/OfferLaws.lean", stub("onWant_keeps")),
      ("engine/world/Hops.lean", stub("onWant_sends"))],
     "engine.world.Members", "engine/world/Members.lean", "recv_shown"),
    ("write-rewrites-held",
     [("engine/wire/Node.lean", "      if (← Store.getOp (F := F) o.id).isNone then absent := o :: absent",
       "      if (← Store.getOp (F := F) o.id).isNone || true then absent := o :: absent"),
      ("engine/world/Run.lean", "  if (!acc.any (·.id == o.id)) && (db.ops o.id).isNone then o :: acc else acc",
       "  if (!acc.any (·.id == o.id)) && ((db.ops o.id).isNone || true) then o :: acc else acc"),
      ("engine/wire/NodeLaws.lean", stub("write_cached")),
      ("ops/sync/OfferLaws.lean", stub("write_ix")),
      ("engine/world/Hops.lean", stub("absent_props"))],
     "engine.world.Idem", "engine/world/Idem.lean", "absentStep_held"),
    ("turn-drains-short",
     [("engine/core/Held.lean", "    ((), { log, db := drainS fam (budget log s) s })\n  purge",
       "    ((), { log, db := drainS fam (budget log s - 1) s })\n  purge"),
      ("engine/world/Run.lean", "  { log := h.log ++ ops, db := drainS fam (budget (h.log ++ ops) s) s }",
       "  { log := h.log ++ ops, db := drainS fam (budget (h.log ++ ops) s - 1) s }"),
      ("engine/wire/NodeLaws.lean", "      ((), Held.mk (h.log ++ ops) (drainS fam (budget (h.log ++ ops) (ops.foldl (fun s o => ingestS o s) h.db))",
       "      ((), Held.mk (h.log ++ ops) (drainS fam (budget (h.log ++ ops) (ops.foldl (fun s o => ingestS o s) h.db) - 1)"),
      ("engine/wire/NodeLaws.lean", stub("write_cached"))],
     "engine.world.Settle", "engine/world/Settle.lean", "turnH_settled"),
    ("lists-unsorted",
     [("engine/core/Query.lean", "  sortPos <| (s.idx q.key).filterMap fun x =>", "  id <| (s.idx q.key).filterMap fun x =>"),
      ("engine/core/Decl.lean", stub("mem_matching")),
      ("engine/core/Decl.lean", stub("matching_nodup")),
      ("engine/core/Order.lean", stub("top_max"))],
     "engine.world.Settle", "engine/world/Settle.lean", "list_eval_congr"),
    # local's view half rests on the engine's Inv (each op once under a
    # key): a store that indexes an op twice is refused by the engine's
    # law that the index keeps each op once, which local takes as given.
    ("index-twice",
     [("engine/core/Model.lean", "  { s with idx := fun i => if i = k then ins (s.idx k) x else s.idx i }",
       "  { s with idx := fun i => if i = k then s.idx k ++ [x] else s.idx i }")],
     "engine.world.Settle", "engine/core/Proofs.lean", "indexAllS_nodup"),
    ("opening-fingerprints-a-leaf",
     [("ops/sync/Round.lean", "  if x.length ≤ P.leaf then .ids r (x.map ident) else .fp r",
       "  if x.length < P.leaf then .ids r (x.map ident) else .fp r"),
      ("engine/world/Pilot.lean", stub("round_forward"))],
     "engine.world.Leaf", "engine/world/Leaf.lean", "opening_ids"),
]
for c in cases:
    if only and c[0] not in only:
        continue
    name, edits, target, wfile, wthm = c
    saved = {}
    try:
        for e in edits:
            path = root / e[0]
            if e[0] not in saved:
                saved[e[0]] = path.read_text()
            text = path.read_text()
            if isinstance(e[1], tuple):
                text = apply_stub(text, e[1][1])
            else:
                assert text.count(e[1]) == 1, (name, e[0], "mutation target missing or ambiguous")
                text = text.replace(e[1], e[2])
            path.write_text(text)
        code = run(["lake", "build", target], name)
        log = (logs / (name + ".log")).read_text()
        s, e = span((root / wfile).read_text(), wthm)
        hits = [int(m.group(1)) for m in re.finditer(re.escape("error: " + wfile) + r":(\d+):", log)]
        inside = [l for l in hits if s <= l < e]
        others = sorted(set(re.findall(r"error: ([\w/]+\.lean):\d+:", log)) - {wfile})
        assert code != 0, (name, "the mutant built")
        assert inside, (name, f"not refused inside {wthm} (lines {s}-{e}); errors at {hits} in {wfile}, and in {others}")
        print(f"refused: {name}, inside {wthm}" + (f" (also {others})" if others else ""), flush=True)
    finally:
        for f, t in saved.items():
            (root / f).write_text(t)
targets = sorted({c[2] for c in cases if not only or c[0] in only})
assert run(["lake", "build", *targets], "restored-build") == 0, "restored sources did not build"
print(f"world negative controls: {len([c for c in cases if not only or c[0] in only])} refused inside their laws; restored targets build")
