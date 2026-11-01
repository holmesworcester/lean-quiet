#!/usr/bin/env python3
"""Actual Reader capability/SQLite controls: only compiled exact failures pass."""
from pathlib import Path
import os
import re
import signal
import subprocess
import sys

root, logs = (Path(value).resolve() for value in sys.argv[1:3])
logs.mkdir(parents=True, exist_ok=True)
cap = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']


def run(args, name, timeout):
    child = subprocess.Popen(args, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (logs / (name + '.log')).write_text(text + '\nTIMEOUT (not an accepted control)\n')
        raise
    (logs / (name + '.log')).write_text(text)
    return child.returncode, text


def build(name):
    code, text = run(cap + ['lake', 'build', 'app_reader_ownership'], name + '-build', 360)
    assert code == 0, (name, 'must compile', text[-3000:])


def exercise(name, expected=()):
    data = logs / (name + '-db')
    code, text = run([str(root / '.lake/build/bin/app_reader_ownership'), str(data)], name, 30)
    assert (data / 'app.db').is_file(), (name, 'missing actual SQLite fixture')
    assert not any(marker in text.lower() for marker in ['panic', 'unexpected reader ownership fixture error',
        'uncaught exception', 'segmentation fault', 'assertion violation']), (name, text)
    failures = [line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    summary = re.search(r'app-reader-ownership: (\d+) passed, (\d+) failed', text)
    assert summary and int(summary[2]) == len(failures), (name, text)
    if expected:
        assert code == 1 and sorted(failures) == sorted(expected), (name, code, failures, text)
    else:
        assert code == 0 and not failures and summary[1] == '26', (name, text)


def once(text, old, new):
    assert text.count(old) == 1, ('production anchor must be unique', old)
    return text.replace(old, new)


source = root / 'app/Screen.lean'
original = source.read_text()
controls = [
    ('forget-worker-slot', lambda s: once(s,
        '    let worker ← Worker.start board state\n    set { n with\n      active := some ⟨worker, board⟩',
        '    let worker ← Worker.start board state\n    set { n with\n      active := none'),
     ['actual mount/resume returned the original Worker capability']),
    ('forget-retiring-slot', lambda s: once(s, '    retiring := n.active\n', '    retiring := none\n'),
     ['suspend retains the original unfinished Reader task for later reap',
      'the retained task is exactly the original Worker and its stop flag']),
    ('omit-original-revocation', lambda s: once(s,
        '  if let some held := n.active then held.worker.requestStop\n',
        '  if let some _ := n.active then pure ()\n'),
     ['suspend revokes the original in-flight Reader despite frame rollback',
      'the original Reader worker finishes after App revocation',
      'revoked in-flight work does not publish its signed write after suspend']),
    ('replace-retiring-generation', lambda s: once(s,
        '  if n.retiring.isSome then return false\n', ''),
     ['another suspend keeps exactly the original retiring Worker',
      'another suspend keeps the replacement board and owner generation']),
    ('discard-reaped-connection', lambda s: once(s,
        '      ready := some { rd := state.rd }\n', '      ready := none\n'),
     ['shared ownership retains the original Reader connection after reap rollback']),
    ('reset-live-cache-on-poll', lambda s: once(s,
        '      else if s.readerGeneration != n.generation then n.ready else s.rst\n',
        '      else n.ready\n'),
     ['same-generation polling retains synchronous Reader cache progress']),
]

build('baseline')
exercise('baseline')
try:
    for name, mutate, expected in controls:
        source.write_text(mutate(original))
        build(name)
        exercise(name, expected)
        print('rejected: ' + name + ' (compiled, exact actual Reader assertion)', flush=True)
finally:
    source.write_text(original)
build('restored')
exercise('restored')
print('app reader ownership:26 actual checks, six compiling controls; restored pass', flush=True)
