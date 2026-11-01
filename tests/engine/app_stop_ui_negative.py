#!/usr/bin/env python3
"""Real suspended Runner: all UI guards must admit foreground service.
Only compiled controls with the exact completed assertion failures pass.
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
    code, text = run(cap + ['lake', 'build', 'app_stop_ui'], name + '-build', 360)
    assert code == 0, (name, 'must compile', text[-3000:])


def exercise(name, expected=()):
    data = logs / (name + '-db')
    code, text = run([str(root / '.lake/build/bin/app_stop_ui'), str(data)], name, 40)
    assert (data / 'app.db').is_file(), (name, 'missing actual SQLite fixture')
    assert not any(marker in text.lower() for marker in ['panic', 'unexpected app stop ui fixture error',
        'uncaught exception', 'segmentation fault', 'assertion violation']), (name, text)
    failures = [line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    summary = re.search(r'app-stop-ui: (\d+) passed, (\d+) failed', text)
    assert summary and int(summary[1]) + int(summary[2]) == 12, (name, text)
    assert int(summary[2]) == len(failures), (name, text)
    assert sorted(failures) == sorted(expected), (name, failures, expected, text)
    assert code == (1 if expected else 0), (name, code, text)


def once(s, a, b):
    assert s.count(a) == 1, ('production anchor must be unique', a)
    return s.replace(a, b)


frame = 'first completed foreground stage publishes a frame during normal cleanup'
mount = 'first completed foreground stage mounts the actual conversation'
reader = 'foreground starts the actual threaded Reader while cleanup remains held'
typing = 'the next completed frame accepts typing during normal cleanup'
answers = 'resumed threaded Reader publishes real SQLite answers before native cleanup'
controls = [
    ('wait-to-frame', 'if !s.active || !s.surface then\n      IO.sleep 16',
     'if !s.active || !s.surface || s.netStop.isSome then\n      IO.sleep 16',
     [frame, mount, reader, typing, answers]),
    ('wait-to-mount', 'if !s.active || !s.surface then return\n  if s.mountedPage',
     'if !s.active || !s.surface || s.netStop.isSome then return\n  if s.mountedPage',
     [mount, reader, typing, answers]),
    ('wait-to-read', 'if !s.threaded || !s.active || !s.surface || s.reader.isSome then return',
     'if !s.threaded || !s.active || !s.surface || s.netStop.isSome || s.reader.isSome then return',
     [reader, answers]),
]
source = root / 'app/Screen.lean'
original = source.read_text()
build('baseline')
exercise('baseline')
try:
    for name, before, after, expected in controls:
        source.write_text(once(original, before, after))
        build(name)
        exercise(name, expected)
        print('rejected: ' + name + ' (compiled, exact completed App assertions)', flush=True)
finally:
    source.write_text(original)
build('restored')
exercise('restored')
print('app normal stop UI:12 actual checks, three compiling controls; restored pass', flush=True)
