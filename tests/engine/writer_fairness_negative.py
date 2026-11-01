#!/usr/bin/env python3
"""Mutate the queue actually called by Writer.loop, never a parallel harness.
All controls must compile and fail the matching signed-op/SQLite assertion.
"""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/writer-fairness'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']
axioms = (OUT / 'axioms.log').read_text()
assert 'sorryAx' not in axioms and 'error:' not in axioms, axioms
assert axioms.count('Data.WriterQueue.') == 11, axioms
for group in re.findall(r'depends on axioms: \[(.*?)\]', axioms, re.S):
    assert set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*', group)) <= {'propext', 'Classical.choice', 'Quot.sound'}, group


def run(root, command, name, timeout=60):
    child = sp.Popen(command, cwd=root, text=True, stdout=sp.PIPE, stderr=sp.STDOUT,
                     start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except sp.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (OUT / (name + '.log')).write_text(text + '\nTIMEOUT\n')
        raise
    (OUT / (name + '.log')).write_text(text)
    return child.returncode, text


def build(root, name):
    code, _ = run(root, CAP + ['lake', 'build', 'writer_fairness'], name + '-build', 300)
    assert code == 0, f'{name}: mutant/restoration must compile; see {OUT}'


def check(root, name, expected=None):
    code, text = run(root, [str(root / '.lake/build/bin/writer_fairness'), str(OUT / (name + '-data'))], name)
    assert not any(marker in text.lower() for marker in ['panic', 'uncaught exception',
        'segmentation fault', 'assertion violation', 'writer:']), text
    if expected:
        assert code == 1 and 'writer-fairness:' in text and 'FAIL: ' + expected in text, (code, text)
    else:
        assert code == 0 and 'writer-fairness: 19 passed, 0 failed' in text, (code, text)


CASES = [
    ('lifo-local',
     'writes := q.writes ++ [job]',
     'writes := job :: q.writes',
     'oldest accepted local commits within two turns despite continuing local arrivals'),
    ('strict-local-priority',
     'let (selected, next) := Priority.step q',
     'let (selected, next) := Priority.step { q with slot := Priority.first }',
     'oldest background commits within four turns under continuing local submissions'),
    ('producer-resets-phase',
     'writes := q.writes ++ [job]',
     'writes := q.writes ++ [job], slot := Priority.first',
     'oldest background commits within four turns under continuing local submissions'),
    ('rebuild-opposite-lane',
     'if job.mine then { q with writes := q.writes ++ [job] }\n  else { q with events := q.events ++ [job] }',
     'if job.mine then q.append [job] [] else q.append [] [job]',
     'actual local submission retains the background backlog without rebuilding it'),
]
check(ROOT, 'baseline')
with tempfile.TemporaryDirectory(prefix='writer-fairness-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
        'engine/renderer engine/sync app tests/engine',
        'writer-fairness-snapshot', str(scratch)], cwd=ROOT, check=True)
    source = scratch / 'engine/renderer/WriteQueue.lean'
    original = source.read_text()
    for name, old, new, expected in CASES:
        assert original.count(old) == 1, f'{name}: ambiguous queue anchor'
        try:
            source.write_text(original.replace(old, new))
            build(scratch, name)
            check(scratch, name, expected)
            print(f'refused: {name} (compiled, actual Writer.loop and SQLite assertion)', flush=True)
        finally:
            source.write_text(original)
    build(scratch, 'restored')
    check(scratch, 'restored')
print('writer fairness: 11 kernel laws, 19 actual-loop/SQLite checks, four compiling controls; restored suite passes', flush=True)
