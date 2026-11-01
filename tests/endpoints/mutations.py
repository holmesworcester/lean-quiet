#!/usr/bin/env python3
"""Each actual-source mutant must fail the same Lean law build.
Scratch copies stay inside this worktree; never modify another checkout.
"""
import argparse, pathlib, shutil, subprocess, tempfile
root = pathlib.Path.cwd()
out = root / 'out/endpoints/mutations'
out.mkdir(parents=True, exist_ok=True)
# name, mutated file, text, replacement, and the law it must break: the file
# and the line that starts that law's declaration. A rejection counts only if
# an error lands inside that declaration (up to the next one), not anywhere in
# the file: every endpoint law shares app/Proofs.lean.
mutants = [
 ('direct_store_write', 'app/Commands.lean', '  let old ← (retryState peer).run', '  Store.putOp (Community.mkOp [] (.retry peer now 0))\n  let old ← (retryState peer).run',
  'app/Proofs.lean', 'private theorem plan_reads'),
 ('drop_ready_plan', 'app/Commands.lean', 'return some (addr, Community.mkOp [] (.retry peer now attempt))', 'return none',
  'app/Proofs.lean', 'theorem plan_ready'),
 ('arrival_wins', 'engine/wire/Winner.lean', 'if bcmp a b = .gt then b else a', 'a',
  'engine/wire/Winner.lean', 'theorem choose_comm'),
 ('uncapped_addresses', 'engine/wire/Address.lean', '.eraseDups.take cap', '.eraseDups',
  'engine/wire/Address.lean', 'theorem bounded_cap'),
 ('expired_still_fresh', 'engine/wire/Address.lean', 'issued ≤ now && now < expires', 'issued ≤ now && now ≤ expires',
  'engine/wire/Address.lean', 'theorem fresh_expires'),
 ('unbounded_backoff', 'engine/wire/Address.lean', 'min 60000 (1000 * 2 ^ min attempts 6)', '(1000 * 2 ^ min attempts 60)',
  'engine/wire/Address.lean', 'theorem delay_bounded'),
 ('retry_every_tick', 'app/Commands.lean', '| some (time, attempts) => Hints.due now time attempts', '| some (_, _) => true',
  'app/Proofs.lean', 'example : Discovery.canTry 1001 (some (1000, 200)) = false'),
 ('unsigned_publication', 'app/community/addresses/Validate.lean', 'C.verify d (signedBy o (Body.unsigned ⟨ds, os, issued, expires, sig⟩)) sig', 'True',
  'app/Proofs.lean', 'theorem publication_auth'),
 ('scan_never_wraps', 'engine/core/Cursor.lean', '  if (past lt key c R).isEmpty && c.isSome then R.take n else (past lt key c R).take n', '  (past lt key c R).take n',
  'engine/core/Cursor.lean', 'theorem dist_step'),
 ('stale_names_newest', 'app/Commands.lean', '  return (rs.drop 1 ++ ds.drop 1).map (·.1.2)', '  return (rs ++ ds.drop 1).map (·.1.2)',
  'app/Proofs.lean', 'theorem olderOf_eval'),
 ('publish_without_gap', 'app/Commands.lean', "    (decide (issued + gap ≤ now) && (ds != ds' || os != os')) || decide (issued + refresh ≤ now)",
  "    (ds != ds' || os != os') || decide (issued + refresh ≤ now)", 'app/Proofs.lean', 'theorem publish_gap'),
 ('attempt_repeats', 'app/Commands.lean', '  | some (_, attempts) => (attempts + 1) % (2^63)', '  | some (_, attempts) => attempts % (2^63)',
  'app/Proofs.lean', 'theorem nextAttempt_eq'),
 ('attempt_without_courier', 'app/Commands.lean', '  | some ro => return [retry, Send.op addr ro]', '  | some ro => return [retry]',
  'app/Proofs.lean', 'theorem attempt_sends'),
 ('flush_keeps_stale', 'engine/wire/Node.lean', '  let e ← Effects.purge x (box.map (·.1) ++ old) false', '  let e ← Effects.purge x (box.map (·.1)) false',
  'engine/wire/CloseLaws.lean', 'theorem flush_notifies'),
]
DECL = ('theorem ', 'private theorem ', 'example', 'def ', '/--', 'end ', 'section', 'namespace ', 'lemma ')

def law_range(path, anchor):
    """The 1-based lines of the declaration that starts with `anchor`."""
    lines = path.read_text().split('\n')
    starts = [i for i, l in enumerate(lines) if l.startswith(anchor)]
    assert len(starts) == 1, (path, anchor, len(starts))
    a = starts[0]
    b = next((i for i in range(a + 1, len(lines)) if lines[i].startswith(DECL)), len(lines))
    return a + 1, b

def broke(logtext, scratch, file, anchor):
    lo, hi = law_range(scratch/file, anchor)
    import re
    for m in re.finditer(r'^error: ' + re.escape(file) + r':(\d+):', logtext, re.M):
        if lo <= int(m.group(1)) <= hi:
            return True
    return False

COPY = ['engine', 'app', 'tests', '.lake', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'third_party', 'platforms']
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--only', choices=[m[0] for m in mutants] + ['unrouted_loser'])
selected = parser.parse_args().only
def run_mutant(m):
    name, file, before, after, lawfile, anchor = m
    scratch = pathlib.Path(tempfile.mkdtemp(prefix=name+'-', dir=out))
    # Reflinks, not hardlinks: build caches and changes belong to this copy.
    for item in COPY:
        subprocess.run(['cp', '-a', '--reflink=auto', str(root/item), str(scratch/item)], check=True)
    p = scratch/file
    data = p.read_text()
    assert data.count(before) == 1, (name, data.count(before))
    p.write_text(data.replace(before, after))
    with (out/(name+'.log')).open('w') as log:
        result = subprocess.run(['lake', 'build', '+app.Proofs'], cwd=scratch, stdout=log, stderr=subprocess.STDOUT)
    logtext = (out/(name+'.log')).read_text()
    if result.returncode == 0 or 'error:' not in logtext:
        return f'Mutant {name} was not rejected; retained {scratch}'
    # Ensure failure was a proof obligation, not a missing artifact/toolchain.
    if not any(marker in logtext.lower() for marker in ['unsolved goals', 'tactic', 'type mismatch', 'omega', 'decide']):
        return f'Mutant {name} failed for an unexpected reason; inspect {scratch}'
    if not broke(logtext, scratch, lawfile, anchor):
        return f'Mutant {name} did not break its intended law ({lawfile}: {anchor}); retained {scratch}'
    shutil.rmtree(scratch)
    return None

import concurrent.futures, os
chosen = [m for m in mutants if not selected or selected == m[0]]
# Each mutant builds in its own copy; a few at a time under the caller's memory cap.
with concurrent.futures.ThreadPoolExecutor(max_workers=int(os.environ.get('LQ_MUTANTS', '4'))) as pool:
    for m, err in zip(chosen, pool.map(run_mutant, chosen)):
        if err:
            raise RuntimeError(err)
        print('REJECTED', m[0], flush=True)
if selected and selected != 'unrouted_loser':
    raise SystemExit(0)
# Socket retirement is a native boundary: require the late losing attempt to
# release its actual socket reservation, not merely disappear from `sessions`.
scratch = pathlib.Path(tempfile.mkdtemp(prefix='unrouted_loser-', dir=out))
for item in COPY:
    subprocess.run(['cp', '-a', '--reflink=auto', str(root/item), str(scratch/item)], check=True)
p = scratch/'app/Commands.lean'
data = p.read_text()
assert data.count('  established := routedSessions') == 1
p.write_text(data.replace('  established := routedSessions', '  established := sessions'))
with (out/'unrouted_loser-build.log').open('w') as log:
    subprocess.run(['lake', 'build', 'endpoint_network'], cwd=scratch, stdout=log, stderr=subprocess.STDOUT, check=True)
with (out/'unrouted_loser.log').open('w') as log:
    result = subprocess.run(['python3', 'tests/endpoints/network.py', 'simultaneous', '--late', '--deadline=12'],
                            cwd=scratch, stdout=log, stderr=subprocess.STDOUT, timeout=45)
logtext = (out/'unrouted_loser.log').read_text()
if result.returncode == 0 or '2 native sockets' not in logtext:
    raise RuntimeError(f'Socket-retirement mutation not rejected for the intended reason: {scratch}')
print('REJECTED unrouted_loser (real TCP socket count)', flush=True)
# Keep its network logs/databases as evidence, including the intentionally failed run.
print('Native retirement mutation artifacts:', scratch, flush=True)
print('PASS ' + ('all endpoint mutation controls' if selected is None else selected))
