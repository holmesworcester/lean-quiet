#!/usr/bin/env python3
"""Require real-code progress and finite junk expiry; reject compiled controls."""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/expiry-grace'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']
axioms = (OUT / 'axioms.log').read_text()
assert 'sorryAx' not in axioms and 'error:' not in axioms, axioms
assert axioms.count('Engine.Sync.ExpiryGrace.') == 11, axioms
for group in re.findall(r'depends on axioms: \[(.*?)\]', axioms, re.S):
    assert set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*', group)) <= {'propext', 'Classical.choice', 'Quot.sound'}, group

def run(root, command, name, timeout=90):
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
    code, _ = run(root, CAP + ['lake', 'build', 'epoch_ingress'], name + '-build', 300)
    assert code == 0, f'{name}: mutant/restoration must compile; see {OUT}'

def check(root, name, expected=None):
    # Real databases must be fresh; retain previous runs rather than delete evidence.
    data = tempfile.mkdtemp(prefix=name + '-data-', dir=OUT)
    code, text = run(root, [str(root / '.lake/build/bin/epoch_ingress'), data], name)
    assert not any(marker in text.lower() for marker in ['panic', 'uncaught exception',
        'segmentation fault', 'assertion violation', 'unexpected diagnostic', 'error:']), text
    if expected:
        assert code == 1 and 'epoch-ingress:' in text and 'FAIL: ' + expected in text, (code, text)
    else:
        assert code == 0 and 'epoch-ingress: 30 passed, 0 failed' in text, (code, text)

CASES = [
    ('no-grace', 'engine/wire/ExpiryGrace.lean', 'def budget (maxSocks : Nat) : Nat := 4 * (maxSocks + 1)',
     'def budget (_maxSocks : Nat) : Nat := 0',
     'UI-first write completes while one-shot grace preserves admitted target'),
    ('pending-rearms-grace', 'engine/wire/ExpiryGrace.lean', 'if s.heard == heard then s else ⟨heard, budget⟩',
     'if s.heard == heard then { s with left := budget } else ⟨heard, budget⟩',
     'sustained untrusted requests cannot reset grace or retain the honest session key'),
    # The shipped retirement close: both directions at once, so the peer's
    # next write met a reset and the peer dropped the unread notice.
    ('reset-on-retirement', 'engine/wire/Tcp.lean',
     '            linger cap c stallMs cleanupReader',
     '            pure ()',
     "retirement resets none of the peer's writes before the peer reads its notice"),
]
check(ROOT, 'baseline')
with tempfile.TemporaryDirectory(prefix='expiry-grace-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
        'engine/renderer engine/sync app tests/engine',
        'expiry-grace-snapshot', str(scratch)], cwd=ROOT, check=True)
    for name, path, old, new, expected in CASES:
        source = scratch / path
        original = source.read_text()
        assert original.count(old) == 1, f'{name}: ambiguous mutation anchor'
        try:
            source.write_text(original.replace(old, new))
            build(scratch, name)
            check(scratch, name, expected)
            print(f'refused: {name} (compiled; real TCP/Noise/SQLite assertion)', flush=True)
        finally:
            source.write_text(original)
    build(scratch, 'restored')
    check(scratch, 'restored')
print('expiry grace: 11 kernel laws, 30 native checks, three compiling controls; restored suite passes', flush=True)
