#!/usr/bin/env python3
"""Require actual frame-path regressions and the kernel capacity control."""
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
    code, text = run(cap + ['lake', 'build', 'app_frame_times'], name + '-build', 360)
    assert code == 0, (name, 'must compile', text[-3000:])


def exercise(name, path=None):
    data = logs / (name + '-db')
    code, text = run([str(root / '.lake/build/bin/app_frame_times'), str(data)], name, 40)
    assert (data / 'app.db').is_file(), (name, 'missing actual SQLite fixture')
    assert not any(marker in text.lower() for marker in ['panic', 'unexpected frame times fixture error',
        'uncaught exception', 'segmentation fault', 'assertion violation']), (name, text)
    failures = [line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    expected = [] if path is None else [path + ': ' + suffix for suffix in [
        'every completed frame retains at most600 timing samples',
        'recorder preserves the existing600/300 policy and sample order',
        'actual recorder reaches the expected post-trim350 samples']]
    summary = re.search(r'app-frame-times: (\d+) passed, (\d+) failed', text)
    assert summary and int(summary[1]) + int(summary[2]) == 9, (name, text)
    assert int(summary[2]) == len(failures), (name, text)
    assert sorted(failures) == sorted(expected), (name, failures, expected, text)
    assert code == (1 if expected else 0), (name, code, text)


def once(s, a, b):
    assert s.count(a) == 1, ('production anchor must be unique', a)
    return s.replace(a, b)


source = root / 'app/Screen.lean'
core = root / 'engine/renderer/FrameTimes.lean'
original, definition = source.read_text(), core.read_text()
build('baseline')
exercise('baseline')
code, text = run(cap + ['lake', 'env', 'lean', 'tests/vacuity/FrameTimes.lean'], 'kernel-witness', 60)
assert code == 0, ('nonempty premise witness must compile', text)
try:
    for name, before, after, path in [
        ('unbounded-page', 'modify fun s => { s with b, frames := s.frames + 1, times := FrameTimes.push s.times (t1 - t0).toNat }',
         'modify fun s => { s with b, frames := s.frames + 1, times := s.times.push (t1 - t0).toNat }', 'non-chat'),
        ('unbounded-chat', 'let times := FrameTimes.push s.times (t1 - t0).toNat',
         'let times := s.times.push (t1 - t0).toNat', 'chat'),
    ]:
        source.write_text(once(original, before, after))
        build(name)
        exercise(name, path)
        print('rejected: ' + name + ' (compiled, exact actual frame assertions)', flush=True)
    source.write_text(original)
    core.write_text(once(definition, 'samples.size ≥ 600', 'samples.size ≥ 601'))
    code, text = run(cap + ['lake', 'build', 'engine.renderer.FrameTimes'], 'kernel-control', 60)
    assert code == 1 and 'error: engine/renderer/FrameTimes.lean:' in text and 'omega could not prove' in text, text
    assert not any(marker in text.lower() for marker in [
        'unknown module', 'unknown constant', 'sorry', 'panic', 'unexpected token',
        'invalid field', 'application type mismatch']), text
    print('rejected: capacity601 (kernel capacity obligation)', flush=True)
finally:
    source.write_text(original)
    core.write_text(definition)
build('restored')
exercise('restored')
print('app frame times:9 actual checks, two runtime controls, one kernel control; restored pass', flush=True)
