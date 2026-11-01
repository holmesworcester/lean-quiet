#!/usr/bin/env python3
"""Mutation controls of the community key (README, "Messages are sealed to
members only").

Each mutant takes one guard out of the code that runs: the wrap's
signature, the post's and attachment's key id, the admission's copy of
the root's key id, unwrap's check of the key it opens, currentKey's and
the approval's reading of the key under the root's id. A proof over that
code must reject it: the build of the mutated tree fails, with an error
inside the named theorem (an error anywhere else is not a rejection).
Mutants work in a scratch snapshot; the working tree is never touched.

  python3 tests/app/community_key_negative.py [mutant...]
"""
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
os.environ.setdefault("ELAN_HOME", "/mnt/storage/elan")
os.environ["PATH"] = os.environ["ELAN_HOME"] + "/bin:" + os.environ["PATH"]
os.environ.setdefault("TMPDIR", "/mnt/storage/holmes-tmp")
LOGS = ROOT / "out/community-key-negative"
LOGS.mkdir(parents=True, exist_ok=True)

WRAP = "app/community/key/wrap/Validate.lean"
POST = "app/community/channel/message/Validate.lean"
ATTACH = "app/community/channel/message/attachment/Validate.lean"
ADMIT = "app/community/member/invite/request/approve/admit/Validate.lean"
CMDS = "app/community/Commands.lean"

# name, [(file, old, new)], theorem, the file it is in, the module to build
cases = [
    ("wrap-unsigned", [
        (WRAP, " ∧ c2 = c ∧ C.verify d (signedBy o (Body.unsigned ⟨bx, s⟩)) s", " ∧ c2 = c"),
    ], "check_wrap", "app/community/key/wrap/Proofs.lean", "app.community.key.wrap.Proofs"),
    ("post-any-kid", [
        (POST, "if o.reqs.head? = some c ∧ u0 = c ∧ k = kid ∧ c1 = c ∧ C.verify",
         "if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ C.verify"),
        (POST, "if o.reqs.head? = some c ∧ u0 = c ∧ k = kid ∧ c1 = c ∧ c2 = c",
         "if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c"),
    ], "check_message", "app/community/channel/message/Proofs.lean", "app.community.channel.message.Proofs"),
    ("attach-any-kid", [
        (ATTACH, "u0 = c ∧ k = kid ∧ c1 = c", "u0 = c ∧ c1 = c"),
    ], "check_attach", "app/community/channel/message/attachment/Proofs.lean",
       "app.community.channel.message.attachment.Proofs"),
    ("admission-no-kid", [
        (ADMIT, "then some ⟨c, u, d, e, kid⟩", "then some ⟨c, u, d, e, .empty⟩"),
    ], "check_admission", "app/community/member/invite/request/approve/admit/Proofs.lean",
       "app.community.member.invite.request.approve.admit.Proofs"),
    ("unwrap-any-key", [
        (CMDS, "(unbox cryptoSeal sk kid bx).filter fun k => decide (kidOf cryptoSeal k = kid)",
         "unbox cryptoSeal sk kid bx"),
    ], "unwrap_community", "app/community/Proofs.lean", "app.community.Proofs"),
    ("currentKey-first-row", [
        (CMDS, "  let some kid ← communityKid c | pure none\n  let ks ← key.byId.read [kid] (limit := some 1)\n",
         "  let ks ← key.byCommunity.read [c] (limit := some 1)\n"),
    ], "currentKey_community", "app/community/Proofs.lean", "app.community.Proofs"),
    ("approval-wraps-any-held-key", [
        (CMDS, "  let k? ← currentKey c\n  match rq.rows.head?, me.rows.head? with",
         "  let ks ← key.byCommunity.read [c] (limit := some 1)\n"
         "  let k? := ks.rows.head?.bind fun (_, f) => match f with | .key _ _ k => Bytes.of? k | _ => none\n"
         "  match rq.rows.head?, me.rows.head? with"),
    ], "approveReq_wrap_admits", "app/community/Proofs.lean", "app.community.Proofs"),
]


def run(args, cwd, name, timeout=1800):
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, timeout=timeout)
    (LOGS / (name + ".log")).write_text(p.stdout)
    return p


def theorem_lines(source, theorem):
    begin = source.index("theorem " + theorem + " ")
    nxt = [source.find(k, begin + 1) for k in ("\ntheorem ", "\ndef ", "\n/--", "\nend ")]
    end = min(i for i in nxt if i != -1)
    return source[:begin].count("\n") + 1, source[:end].count("\n") + 1


if sys.argv[1:]:
    selected = set(sys.argv[1:])
    assert selected <= {c[0] for c in cases}, "unknown mutant"
    cases = [c for c in cases if c[0] in selected]

with tempfile.TemporaryDirectory(prefix="community-key-negative-", dir=os.environ["TMPDIR"]) as tmp:
    base, work = Path(tmp) / "base", Path(tmp) / "work"
    snap = run(["bash", "-c", '. tests/snapshot.sh\nsnapshot "$1" engine/core engine/wire engine/sync engine/renderer app', "snapshot", str(base)],
               ROOT, "snapshot")
    assert snap.returncode == 0, "snapshot failed"
    modules = sorted({c[4] for c in cases})
    assert run(["lake", "build", *modules], base, "baseline-build").returncode == 0, "baseline build failed"
    for name, changes, theorem, tfile, module in cases:
        shutil.copytree(base, work, symlinks=True)
        try:
            for file, old, new in changes:
                path = work / file
                source = path.read_text()
                assert source.count(old) == 1, (name, "missing mutation anchor", old)
                path.write_text(source.replace(old, new))
            p = run(["lake", "build", module], work, name)
            first, last = theorem_lines((work / tfile).read_text(), theorem)
            errors = [(f, int(n)) for f, n in re.findall(r"error: ([^:\s]+\.lean):(\d+):\d+", p.stdout)]
            inside = [e for e in errors if e[0] == tfile and first <= e[1] < last]
            assert p.returncode != 0 and inside, (name, "survived, or rejected elsewhere", errors[:5])
            print(f"rejected {name} by the proof of {theorem}", flush=True)
        finally:
            shutil.rmtree(work)
print(f"community key: all {len(cases)} mutants rejected by proofs of the running code", flush=True)
