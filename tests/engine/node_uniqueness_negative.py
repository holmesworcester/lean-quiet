#!/usr/bin/env python3
"""Require native success, compiling runtime controls, and kernel rejection."""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/node-uniqueness/controls'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']


def run(root, command, name, timeout=300):
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


def build(root, name, target='node_uniqueness', success=True):
    code, text = run(root, CAP + ['lake', 'build', target], name + '-build', 600)
    if success:
        assert code == 0, f'{name}: compilation failure is not a successful control'
    else:
        errors = re.findall(r'^error: ([^\n]+)$', text, re.M)
        assert code > 0 and any(e.startswith('engine/wire/NodeUniqueLaws.lean:') for e in errors), text
        assert all(e.startswith('engine/wire/NodeUniqueLaws.lean:') or e == 'build failed'
                   for e in errors), errors
        assert not any(marker in text for marker in ['unknown identifier', 'Unknown identifier',
            'unexpected token', 'unterminated', 'failed to synthesize',
            'unknown module prefix', 'Unknown module prefix', 'sorry', 'placeholder',
            'object file', 'failed to read', 'unable to load']), text


REPLACE = 'actual repeat-open replaces the existing session ID'
SWEEP = 'actual nonempty retry sweep retains each session once'
ALLOWED = {
    'both actual bootstrapped Nodes have unique session IDs',
    'every completed write frame and timer prefix retains uniqueness',
    'repeated actual established rows do not duplicate live IDs',
    SWEEP, 'repeated actual retry sweeps do not duplicate queue entries', REPLACE,
    'actual transport close removes sessions while preserving retry uniqueness',
}


def check(root, name, required=None):
    data = tempfile.mkdtemp(prefix=name + '-data-', dir=OUT)
    code, text = run(root, [str(root / '.lake/build/bin/node_uniqueness'), data], name, 90)
    assert not any(marker in text.lower() for marker in ['panic', 'uncaught exception',
        'segmentation fault', 'error:', 'unexpected diagnostic']), text
    failures = set(re.findall(r'^FAIL: (.+)$', text, re.M))
    if required:
        assert code == 1 and required in failures and failures <= ALLOWED, (code, text)
        assert re.search(r'node-uniqueness: \d+ passed, \d+ failed', text), text
    else:
        assert code == 0 and 'node-uniqueness: 10 passed, 0 failed' in text, (code, text)
    print(text, end='', flush=True)


check(ROOT, 'baseline')
with tempfile.TemporaryDirectory(prefix='node-uniqueness-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
        'engine/renderer engine/sync app tests/engine', 'node-uniqueness-snapshot', str(scratch)],
        cwd=ROOT, check=True)
    source = scratch / 'engine/wire/Node.lean'
    original = source.read_text()
    cases = [
        ('duplicate-on-follow',
         "n := { n' with managed := cid :: n'.managed }",
         "n := { n' with conns := n'.conns ++ n'.conns, managed := cid :: n'.managed }",
         'both actual bootstrapped Nodes have unique session IDs'),
        ('duplicate-retry-order',
         'let order := RetryOrder.reconcile (n.conns.map Prod.fst) n.retryOrder',
         'let order := n.conns.map Prod.fst ++ n.conns.map Prod.fst', SWEEP),
    ]
    for name, old, new, required in cases:
        assert original.count(old) == 1, f'{name}: ambiguous mutation anchor'
        try:
            source.write_text(original.replace(old, new))
            build(scratch, name)
            check(scratch, name, required)
            build(scratch, name + '-kernel', 'engine.wire.NodeUniqueLaws', success=False)
            print(f'refused: {name} (compiled runtime assertions and unchanged proof)', flush=True)
        finally:
            source.write_text(original)
    try:
        old = 'let n := (n.close cid).setAddr cid addr'
        assert original.count(old) == 1
        source.write_text(original.replace(old, 'let n := n.setAddr cid addr'))
        build(scratch, 'skip-open-replacement-kernel', 'engine.wire.NodeUniqueLaws', success=False)
        print('refused: skip-open-replacement (unchanged proof; runtime imports already reject it)', flush=True)
    finally:
        source.write_text(original)
    build(scratch, 'restored')
    build(scratch, 'restored-kernel', 'engine.wire.NodeUniqueLaws')
    check(scratch, 'restored')
print('node uniqueness: 10 native checks, 2 compiling controls, 3 kernel controls, restored pass', flush=True)
