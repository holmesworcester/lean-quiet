#!/usr/bin/env python3
"""Actual Reader/SQLite batch ownership, with strict compiling controls."""
from pathlib import Path
import shutil
import subprocess
import sys

root, logs = map(Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)
source = root / 'app/Screen.lean'
original = source.read_text()


def run(args, name):
    try:
        result = subprocess.run(args, cwd=root, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, timeout=240)
    except subprocess.TimeoutExpired as error:
        output = error.stdout or b''
        if isinstance(output, bytes):
            output = output.decode(errors='replace')
        (logs / (name + '.log')).write_text(output + '\nTIMEOUT\n')
        raise
    (logs / (name + '.log')).write_text(result.stdout)
    return result


def build(name):
    result = run(['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G',
                  '-p', 'MemorySwapMax=0', 'lake', 'build', 'reader_claim_rollback'], name)
    assert result.returncode == 0, (name, 'control must compile')


def exercise(name, failures=()):
    try:
        result = run([str(root / '.lake/build/bin/reader_claim_rollback')], name)
    finally:
        runtime = root / 'out/reader-claim/runtime'
        if runtime.exists():
            shutil.copytree(runtime, logs / (name + '-db'), dirs_exist_ok=True)
    assert (logs / (name + '-db/fault.db')).is_file(), 'missing native database evidence'
    assert not any(s in result.stdout.lower() for s in
                   ['panic', 'uncaught exception', 'segmentation fault', 'assertion violation'])
    actual = {line.removeprefix('FAIL: ') for line in result.stdout.splitlines()
              if line.startswith('FAIL: ')}
    assert actual == set(failures), (name, actual, failures)
    assert result.returncode == (1 if failures else 0), (name, result.stdout)
    assert f'reader_claim_rollback: {29-len(failures)} passed, {len(failures)} failed' in result.stdout


def once(text, old, new):
    assert text.count(old) == 1, ('anchor is not unique', old)
    return text.replace(old, new)


claim = '    sh.acts.modify fun a => a.extract acts.size a.size\n'
ack = 'sh.notes.modify fun a => a.extract noteCount a.size'
assert original.count(ack) == 2

early = once(original, '  let notes ← sh.notes.get\n',
             '  let notes ← sh.notes.modifyGet fun a => (a, #[])\n')
early = once(early, '  let acts ← sh.acts.get\n',
             '  let acts ← sh.acts.modifyGet fun a => (a, #[])\n')
early = once(early, claim, '')
early = early.replace('      '+ack+'\n', '').replace('    '+ack+'\n', '')

precommit = original.replace('      '+ack+'\n', '').replace('    '+ack+'\n', '')
precommit = once(precommit, claim, claim+'    '+ack+'\n')

controls = [
    ('early-batch-claim', early, [
        'fault: every accepted action still has exactly one owner or result',
        'fault: unprocessed notice remains available after journal rollback',
        'fault: healthy retry invokes accepted intent exactly once',
        'fault: healthy retry reports exactly one judged founding write',
        'cancel: reader has not claimed the revoked captured batch',
        'notes: query failure retains the captured local notices',
        'notes: healthy retry refreshes cached count from pending founding',
        'begin: failed transaction startup preserves accepted action and note',
        'begin: healthy retry invokes retained intent once',
        'begin: healthy retry produces a judged completion']),
    ('drop-new-actions', once(original, claim, '    sh.acts.modify fun _ => #[]\n'), [
        'late: newly appended action retains its own next-pass owner',
        'late: next action reads the newer actual SQLite snapshot exactly once',
        'late: both actions finish and both original notes are consumed']),
    ('early-note-ack', precommit, [
        'notes: query failure retains the captured local notices',
        'notes: healthy retry refreshes cached count from pending founding']),
    ('uncaptured-note-ack', original.replace(ack, 'sh.notes.modify fun a => a.extract notes.size a.size'), [
        'late: only original note prefix is acknowledged despite generated act notices']),
    ('leaked-cancelled-transaction', once(original,
        '    afterJournal\n    if !(← (← get).enabled) then\n      rd.exec "COMMIT"\n      return false\n',
        '    afterJournal\n    if !(← (← get).enabled) then\n      return false\n'), [
        'cancel: early return leaves no open SQLite transaction'])]

build('baseline-build')
exercise('baseline')
try:
    for name, text, failures in controls:
        source.write_text(text)
        (logs / (name + '.lean')).write_text(text)
        build(name+'-build')
        exercise(name, failures)
        print('rejected:', name, flush=True)
finally:
    source.write_text(original)
build('restored-build')
exercise('restored')
print('reader claim: 29 native checks, five compiling controls and restored source pass', flush=True)
