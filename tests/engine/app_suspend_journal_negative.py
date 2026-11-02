#!/usr/bin/env python3
"""Normal suspend recovery using actual App, Runner, Writer and SQLite.
Mutations compile separately and must finish with exactly the intended
assertions. Timeouts, signals, build failures and unexpected exceptions fail.
"""
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
    child = subprocess.Popen(args, cwd=root, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, start_new_session=True)
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
    code, text = run(cap + ['lake', 'build', 'app_suspend_journal'], name + '-build', 360)
    assert code == 0, (name, 'must compile', text[-3000:])


def exercise(name, mode='all', failures=()):
    data = logs / (name + '-db')
    code, text = run([str(root / '.lake/build/bin/app_suspend_journal'), str(data), mode], name, 40)
    modes = ['failure', 'clean', 'held-stop'] if mode == 'all' else [mode]
    for item in modes:
        assert (data / item / 'app.db').is_file(), (name, 'actual SQLite file absent', item)
    assert not any(marker in text.lower() for marker in [
        'panic', 'unexpected app suspend fixture error', 'uncaught exception',
        'segmentation fault', 'assertion violation']), (name, text)
    observed = [line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    summary = re.search(r'app-suspend-journal: (\d+) passed, (\d+) failed', text)
    assert summary and int(summary[2]) == len(observed), (name, text)
    expected_errors = sum(item != 'clean' for item in modes)
    assert text.count('network runner stopped: expected normal-suspend post-commit hook failure') == expected_errors, (name, text)
    if failures:
        assert code == 1 and set(observed) == set(failures), (name, code, observed, text)
    else:
        assert code == 0 and not observed and summary[1] == '51', (name, text)


def once(source, old, new):
    assert source.count(old) == 1, ('production anchor must be unique', old)
    return source.replace(old, new)


source = root / 'app/Screen.lean'
original = source.read_text()
missing = [
    'all previously channel-admitted signed writes commit after normal resume',
    'actual catalog preserves accepted order across stop replay and later writes',
    'replayed already committed operations retain exactly one catalog entry',
    'App journal retires recovered bytes only after actual store observation',
]
controls = [
    ('replay-only-parked', 'failure', lambda value: once(value,
        's.netOwner.retire s.wr s.queuedWrites false',
        's.netOwner.retire s.wr (s.toNode.toList.flatten.map Op.bytes) false'), missing),
    ('replay-before-loop-completion', 'failure', lambda value: once(value,
        '  if let some r := net then discard <| IO.wait r.done\n',
        '  if let some _ := net then pure ()\n'),
        ["replay does not overtake the original runner's unfinished SQLite handler"]),
    ('replay-after-native-stop', 'held-stop', lambda value: once(value,
        '  if let some r := net then discard <| IO.wait r.done\n',
        '  stopNodes boot net\n'),
        ['journal replay uses loop completion without waiting for held App-owned stop call']),
]

build('baseline')
exercise('baseline')
try:
    for name, mode, mutate, failures in controls:
        source.write_text(mutate(original))
        build(name)
        exercise(name, mode, failures)
        print('rejected: ' + name + ' (compiled, exact actual App/SQLite assertion)', flush=True)
finally:
    source.write_text(original)
build('restored')
exercise('restored')
print('app normal suspend: 51 actual checks, three compiling controls; restored pass', flush=True)
