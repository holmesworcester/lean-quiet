#!/usr/bin/env python3
"""Each actual-source mutant must fail the same Lean law build.
Scratch copies stay inside this worktree; never modify another checkout.
"""
import pathlib, shutil, subprocess, tempfile
root = pathlib.Path.cwd()
out = root / 'out/endpoints/mutations'
out.mkdir(parents=True, exist_ok=True)
mutants = [
 ('arrival_wins', 'ops/connection/Winner.lean', 'if bcmp a b = .gt then b else a', 'a'),
 ('uncapped_addresses', 'engine/wire/Address.lean', '.eraseDups.take cap', '.eraseDups'),
 ('expired_still_fresh', 'engine/wire/Address.lean', 'now < expires', 'now ≤ expires'),
 ('unbounded_backoff', 'engine/wire/Address.lean', 'min 60000 (1000 * 2 ^ min attempts 6)', '(1000 * 2 ^ min attempts 60)'),
 ('retry_every_tick', 'ops/connection/Discovery.lean', '| some (time, attempts) => Endpoint.due now time attempts', '| some (_, _) => true'),
 ('unsigned_publication', 'ops/community/Facts.lean', 'C.verify d (signed o (.addresses ds os issued expires sig)) sig', 'True'),
]
for name, file, before, after in mutants:
    scratch = pathlib.Path(tempfile.mkdtemp(prefix=name+'-', dir=out))
    # Reflinks, not hardlinks: build caches and changes belong to this copy.
    for item in ['engine', 'ops', 'tests', '.lake', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'third_party']:
        subprocess.run(['cp', '-a', '--reflink=auto', str(root/item), str(scratch/item)], check=True)
    p = scratch/file
    data = p.read_text()
    assert data.count(before) == 1, (name, data.count(before))
    p.write_text(data.replace(before, after))
    with (out/(name+'.log')).open('w') as log:
        result = subprocess.run(['lake', 'build', '+ops.connection.DiscoveryLaws'], cwd=scratch, stdout=log, stderr=subprocess.STDOUT)
    logtext = (out/(name+'.log')).read_text()
    if result.returncode == 0 or 'error:' not in logtext:
        raise RuntimeError(f'Mutant {name} was not rejected; retained {scratch}')
    # Ensure failure was a proof obligation, not a missing artifact/toolchain.
    if not any(marker in logtext for marker in ['unsolved goals', 'Tactic', 'Type mismatch', 'omega could not prove']):
        raise RuntimeError(f'Mutant {name} failed for an unexpected reason; inspect log')
    print('REJECTED', name, flush=True)
    shutil.rmtree(scratch)
print('PASS all endpoint mutation controls')
