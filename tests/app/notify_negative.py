#!/usr/bin/env python3
"""Negative controls of notifications and Sync in the background.

Works in a snapshot (tests/snapshot.sh) under $TMPDIR, never the working
tree. Each runtime mutant must compile and then fail its named check of
the `notify` headless test; each proof mutant must break the law it names,
inside that law's proof. Logs in out/notify/negative.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
os.environ.setdefault("ELAN_HOME", "/mnt/storage/elan")
os.environ["PATH"] = os.environ["ELAN_HOME"] + "/bin:" + os.environ["PATH"]
os.environ.setdefault("TMPDIR", "/mnt/storage/holmes-tmp")
LOGS = ROOT / "out/notify/negative"
LOGS.mkdir(parents=True, exist_ok=True)


def run(args, cwd, name, timeout=1800):
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, timeout=timeout)
    (LOGS / (name + ".log")).write_text(p.stdout)
    return p


SCREEN = "app/community/Screen.lean"
APP = "app/Screen.lean"

# (name, [(file, old, new)], the check that must fail)
runtime = [
    ("own-alerts", [(SCREEN, "{ device := i.device, authorDevice := r.device, ownUser := decide (r.author = i.user), live := i.live,",
                     "{ device := .empty, authorDevice := r.device, ownUser := false, live := i.live,")],
     "FAIL A's own post does not alert A"),
    ("repeats-alert", [(APP, "Notify.step s.notes present v [] ins", "Notify.step {} present v [] ins")],
     "FAIL a post alerts once, however many turns run"),
    ("screen-not-quiet", [(APP, "if s.active && s.surface && s.page == .chat && !s.me.waiting then some s.me.c else none", "none")],
     "FAIL opening the conversation withdraws its card"),
    ("level-ignored", [(SCREEN, "return ({ rows, mark, read := st.read, settings := st.settings }, d)",
                        "return ({ rows, mark, read := st.read, settings := {} }, d)")],
     "FAIL Off silences"),
    ("history-alerts", [(SCREEN, "news := (match i.snap.mark with | some m => decide (m ≤ r.time) | none => false),",
                         "news := true,")],
     "FAIL and nothing alerted for the community's history"),
    ("link-at-newest", [(APP, "  modify fun s => targetSt s t p ((viewH s) * 2 / 3)",
                         "  modify fun s => { s.withNav (Nav.go .chat s.nav) with pendingTarget := none }")],
     "FAIL the card's link opens the conversation with its message wholly on screen"),
    ("background-stops", [(APP, "if s.keepSync && s.netStop.isNone then backgroundStep", "if false then backgroundStep")],
     "FAIL with Sync in the background on, a post arriving in the background alerts"),
    ("background-ignores-off", [(APP, "if s.keepSync && s.netStop.isNone then backgroundStep", "if s.netStop.isNone then backgroundStep")],
     "FAIL with it off, nothing alerts while in the background"),
    ("removal-kept", [(APP, "live := !m.waiting && !m.removed, snap := snap", "live := !m.waiting, snap := snap")],
     "FAIL B's removal withdraws its standing card"),
    ("policy-replies-all", [(SCREEN, "  else if m.reply then", "  else if false then")],
     "FAIL the policy is libquiet's on all 20736 reference cases"),
]

# (name, file, old, new, the law whose proof must break)
proofs = [
    ("eligible-ignores-screen", SCREEN, "  !f.visible && !f.read && policy s f.subject", "  !f.read && policy s f.subject", "step_quiet"),
    ("gone-keeps-reads", SCREEN, "decide (viewing = some c.community) || Engine.has reads c.id ||", "decide (viewing = some c.community) ||", "step_read"),
    ("gone-keeps-left", SCREEN, "|| !Engine.has present c.community ||", "||", "step_removed"),
    ("mark-ahead", SCREEN, "      let top := min now (i.snap.rows.foldl (fun t r => max t r.time) 0)",
     "      let top := i.snap.rows.foldl (fun t r => max t r.time) 0", "marks_le"),
    ("notice-unsigned", "app/community/notice/Validate.lean", " ∧ bx.size ≤ maxBox ∧\n      C.verify d (signedBy o (Body.unsigned ⟨r, bx, tm, s⟩)) s",
     " ∧ bx.size ≤ maxBox", "check_notice"),
    ("link-drops-root", "app/community/Commands.lean", "(encode (linkVersion, t.community, t.conversation, t.message, t.root))",
     "(encode (linkVersion, t.community, t.conversation, t.message, ([] : List Id)))", "target_roundtrip"),
    ("toggle-drops-writes", APP, "def keepSyncSt (s : St) (on : Bool) : St := { s with keepSync := on && s.canKeep, pageKey := none }",
     "def keepSyncSt (s : St) (on : Bool) : St := { s with keepSync := on && s.canKeep, pageKey := none, toNode := #[] }", "keepSync_keeps"),
    ("background-stops-sync", APP, "def St.syncs (s : St) : Bool := s.active && s.surface || s.keepSync",
     "def St.syncs (s : St) : Bool := s.active && s.surface", "syncs_kept"),
]

LAWFILE = {"step_quiet": SCREEN, "step_read": SCREEN, "step_removed": SCREEN, "marks_le": SCREEN,
           "check_notice": "app/community/notice/Proofs.lean", "target_roundtrip": "app/community/Proofs.lean",
           "keepSync_keeps": "app/Proofs.lean", "syncs_kept": "app/Proofs.lean"}
MODULE = {SCREEN: "app.community.Screen", APP: "app.Proofs",
          "app/community/notice/Validate.lean": "app.community.notice.Proofs",
          "app/community/Commands.lean": "app.community.Proofs"}

only = set(sys.argv[1:])
names = {c[0] for c in runtime} | {c[0] for c in proofs}
assert only <= names, "unknown mutation"

with tempfile.TemporaryDirectory(prefix="notify-negative-", dir=os.environ["TMPDIR"]) as tmp:
    base, work = Path(tmp) / "base", Path(tmp) / "work"
    snap = run(["bash", "-c", '. tests/snapshot.sh\nsnapshot "$1" engine app platforms/headless tests/app tests/engine Quiet.lean assets',
                "snapshot", str(base)], ROOT, "snapshot")
    assert snap.returncode == 0, "snapshot failed"
    assert run(["lake", "build", "notify", "app.Proofs"], base, "baseline-build").returncode == 0, "baseline build failed"
    p = run([str(base / ".lake/build/bin/notify"), str(LOGS / "baseline")], base, "baseline")
    assert p.returncode == 0 and "notify: all pass" in p.stdout, "baseline failed"
    for name, changes, expected in runtime:
        if only and name not in only:
            continue
        shutil.copytree(base, work, symlinks=True)
        try:
            for file, old, new in changes:
                path = work / file
                source = path.read_text()
                assert source.count(old) == 1, (name, "missing mutation anchor", old)
                path.write_text(source.replace(old, new))
            # the laws may break too; the runtime check must still catch it
            b = run(["lake", "build", "notify"], work, name + "-build")
            assert b.returncode == 0, (name, "must compile before runtime rejection")
            p = run([str(work / ".lake/build/bin/notify"), str(LOGS / name)], work, name)
            assert p.returncode == 1 and expected in p.stdout, (name, "survived or wrong failure", p.stdout[-1500:])
            print("rejected", name, flush=True)
        finally:
            shutil.rmtree(work)
    for name, file, old, new, law in proofs:
        if only and name not in only:
            continue
        shutil.copytree(base, work, symlinks=True)
        try:
            path = work / file
            source = path.read_text()
            assert source.count(old) == 1, (name, "missing proof anchor")
            path.write_text(source.replace(old, new))
            p = run(["lake", "build", MODULE[file]], work, name + "-proof")
            lawsrc = (work / LAWFILE[law]).read_text()
            begin = lawsrc.index("theorem " + law)
            end = lawsrc.find("\ntheorem ", begin + 1)
            end = len(lawsrc) if end < 0 else end
            first = lawsrc[:begin].count("\n") + 1
            last = lawsrc[:end].count("\n") + 1
            pat = re.escape(LAWFILE[law]) + r":(\d+):\d+: error"
            lines = [int(n) for n in re.findall(pat, p.stdout)]
            assert p.returncode != 0 and any(first <= n <= last for n in lines), \
                (name, "proof mutant survived or broke elsewhere", p.stdout[-1500:])
            print("rejected", name, "by", law, flush=True)
        finally:
            shutil.rmtree(work)
print("notify negative: all rejected")
