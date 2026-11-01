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
for name, file, before, after, lawfile, anchor in mutants:
    if selected and selected != name:
        continue
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
        raise RuntimeError(f'Mutant {name} was not rejected; retained {scratch}')
    # Ensure failure was a proof obligation, not a missing artifact/toolchain.
    if not any(marker in logtext.lower() for marker in ['unsolved goals', 'tactic', 'type mismatch', 'omega', 'decide']):
        raise RuntimeError(f'Mutant {name} failed for an unexpected reason; inspect log')
    if not broke(logtext, scratch, lawfile, anchor):
        raise RuntimeError(f'Mutant {name} did not break its intended law ({lawfile}: {anchor})')
    print('REJECTED', name, flush=True)
    shutil.rmtree(scratch)
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
