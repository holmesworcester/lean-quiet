#!/usr/bin/env python3
"""Actual failed-runner recovery; no timeout, crash, or build failure is a control pass.

The fixture owns a real Writer queue token and real Runner closing mutex.
Its unsafe Ref gate is Linux SDK fixture instrumentation, not a concurrency proof.
Each process has bounded cleanup and retains its SQLite files outside the snapshot.
"""
from pathlib import Path
import os
import re
import signal
import subprocess
import sys

root, logs = map(lambda value: Path(value).resolve(), sys.argv[1:3])
logs.mkdir(parents=True, exist_ok=True)
cap = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']
lake = ['lake'] + (['-f', sys.argv[3]] if len(sys.argv) == 4 else [])


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
    code, text = run(cap + lake + ['build', 'app_runner_failure'], name, 300)
    assert code == 0, (name, 'must compile', text[-3000:])


def exercise(name, mode='all', required=(), permitted=()):
    data = logs / (name + '-db')
    code, text = run([str(root / '.lake/build/bin/app_runner_failure'), str(data), mode], name, 30)
    modes = ['flush', 'network', 'suspend'] if mode == 'all' else [mode]
    for entry in modes:
        assert (data / entry / 'app.db').is_file(), (name, 'missing actual SQLite fixture', entry)
    assert not any(marker in text.lower() for marker in [
        'panic', 'unexpected app runner fixture error', 'uncaught exception',
        'segmentation fault', 'assertion violation']), (name, text)
    failures = [line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    summary = re.search(r'app-runner-failure: (\d+) passed, (\d+) failed', text)
    assert summary, (name, 'missing completed fixture summary', text)
    assert int(summary[2]) == len(failures), (name, text)
    assert text.count('network runner stopped: expected AppRunnerFailure post-commit hook failure') == len(modes), (name, text)
    if not required:
        assert code == 0 and not failures and summary[1] == '77', (name, text)
    else:
        assert code == 1 and set(required) <= set(failures), (name, text)
        assert set(failures) <= set(permitted or required), (name, 'unexpected assertion failures', text)


def once(text, old, new):
    assert text.count(old) == 1, ('unique production anchor changed', old)
    return text.replace(old, new)


source = root / 'app/Screen.lean'
original = source.read_text()
entry = 'entry stage detects the finished runner even with an empty parked queue'
replay = 'replay reaches real queue admission off the App thread'
admission = 'new action parks without a second actual writer admission'
parked = 'later local action remains parked until replay submission is observed'
ui = 'failed teardown does not use the flag that suppresses active App frames'
stopped = 'the retained recovery task actually stops its failed runner'
unfinished = 'failed teardown retains its actual unfinished task'

controls = [
    ('omit-flush-observation', 'flush', lambda s: once(s,
        'def flushNode : M Unit := do\n  recoverNode\n',
        'def flushNode : M Unit := do\n'), [entry], []),
    ('omit-network-observation', 'network', lambda s: once(s,
        'def netStep : M Unit := do\n  recoverNode\n',
        'def netStep : M Unit := do\n'), [entry], []),
    ('omit-suspend-observation', 'suspend', lambda s: once(s,
        '  let deadline := (← IO.monoMsNow) + budget\n  recoverNode\n',
        '  let deadline := (← IO.monoMsNow) + budget\n'), [entry], []),
    ('replay-only-parked', 'flush', lambda s: once(s,
        '(replayNodeWrites s.wr s.queuedWrites)',
        '(replayNodeWrites s.wr (s.toNode.toList.flatten.map Op.bytes))'), [replay], []),
    ('eager-write-during-replay', 'flush', lambda s: once(once(s,
        's.netStop.isSome || s.netReplay.isSome || s.toNode.isEmpty',
        's.netStop.isSome || s.toNode.isEmpty'),
        's.netBoot.isSome || s.netStop.isSome || s.netReplay.isSome then',
        's.netBoot.isSome || s.netStop.isSome then'), [admission, parked], []),
    ('failed-stop-suppresses-ui', 'flush', lambda s: once(s,
        'netReplay := some replay, failedNetStop := some stopping,',
        'netReplay := some replay, netStop := some stopping,'), [ui], []),
    ('omit-actual-failed-stop', 'flush', lambda s: once(s,
        'let stopping ← IO.asTask (prio := .dedicated) (stopNodes none (some r))',
        'let stopping ← IO.asTask (prio := .dedicated) (pure () : IO Unit)'),
        [stopped], [stopped, unfinished]),
]

build('baseline-build')
exercise('baseline')
try:
    for name, mode, mutate, required, permitted in controls:
        source.write_text(mutate(original))
        build(name + '-build')
        exercise(name, mode, required, permitted)
        print('rejected: ' + name + ' (compiled, intended actual App assertion)', flush=True)
finally:
    source.write_text(original)
build('restored-build')
exercise('restored')
print('app runner failure: 77 actual checks, seven compiling controls; restored pass', flush=True)
