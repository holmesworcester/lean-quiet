#!/usr/bin/env python3
"""Require actual SQLite write service despite a failed checkpoint.

The old recursion is released by the fixture after three real SQL errors.
Only its exact completed assertion failures count, never a timeout/crash.
"""
from pathlib import Path
import os
import signal
import subprocess
import sys

root, logs = map(lambda value: Path(value).resolve(), sys.argv[1:3])
logs.mkdir(parents=True, exist_ok=True)
cap = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']
# A reusable private diagnostic tree can supply an additive Lake config;
# CI uses the checked-in lakefile and the same target, fixture and controls.
lake = ['lake'] + (['-f', sys.argv[3]] if len(sys.argv) == 4 else [])


def run(args, name):
    child = subprocess.Popen(args, cwd=root, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        text, _ = child.communicate(timeout=240)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (logs / (name + '.log')).write_text(text + '\nTIMEOUT\n')
        raise
    (logs / (name + '.log')).write_text(text)
    return child.returncode, text


def build(name):
    code, text = run(cap + lake + ['build', 'writer_checkpoint'], name)
    assert code == 0, (name, 'must compile', text[-2000:])


failures = [
    'one actual writer turn attempts the failing checkpoint exactly once',
    'signed write is readable while the actual checkpoint table remains unavailable',
    'failed checkpoint remains pending and unacknowledged after write service',
    'newer checkpoint arriving during failure is retained for the next turn',
    'newer checkpoint arriving during success remains pending and unacknowledged',
    'the following actual turn commits and acknowledges the latest generation',
]


def exercise(name, good):
    data = logs / (name + '-db')
    code, text = run([str(root / '.lake/build/bin/writer_checkpoint'), str(data)], name)
    assert (data / 'failure/publication.db').is_file(), (name, 'missing failure database')
    assert (data / 'generations/publication.db').is_file(), (name, 'missing generation database')
    assert not any(marker in text.lower() for marker in [
        'panic', 'uncaught exception', 'segmentation fault', 'assertion violation']), (name, text)
    actual = [line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    if good:
        assert code == 0 and 'writer-checkpoint: 12 passed, 0 failed' in text and not actual, (name, text)
        assert 'attempts=1, SQL errors=1, selected=true, readable=true, checkpointTable=false, pending=true, saved=0' in text, (name, text)
    else:
        assert code == 1 and 'writer-checkpoint: 6 passed, 6 failed' in text and actual == failures, (name, text)
        assert 'attempts=4, SQL errors=3, selected=true, readable=true, checkpointTable=true, pending=false, saved=1' in text, (name, text)


build('baseline-build')
exercise('baseline', True)
source = root / 'app/Commands.lean'
original = source.read_text()
definition = 'def Writer.commitSave (w : Writer)'
backoff = '    discard <| (IO.eprintln s!"writer: checkpoint: {e}").toBaseIO\n    IO.sleep 50\n'
assert original.count(definition) == 1 and original.count(backoff) == 1, 'unique production anchors changed'
try:
    source.write_text(original.replace(definition, 'partial ' + definition).replace(
        backoff, backoff + '    w.commitSave db save\n'))
    build('recursive-build')
    exercise('recursive', False)
    print('rejected: recursive checkpoint retry before the selected real write', flush=True)
finally:
    source.write_text(original)
build('restored-build')
exercise('restored', True)
print('writer checkpoint: 12 actual SQLite checks, strict compiling recursive control, restored pass', flush=True)
