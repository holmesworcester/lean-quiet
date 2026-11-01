#!/usr/bin/env python3
"""Production publication operations, real SQLite effects, exact SDK overlap.
Each old direct-set control must compile, enter the getter window, complete
publication while the read is paused, and fail the matching runtime assertion.
"""
from pathlib import Path
import os
import signal
import subprocess as sp
import sys
import tempfile
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import mutants

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/ref-publications'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']
CASES = [
    ('checkpoint', 'checkpoint_ack', [], 'app/Commands.lean',
     'w.saved.modify (fun _ => n)', 'w.saved.set n',
     'committed checkpoint remains acknowledged after the overlapping old read',
     'checkpoint-ack: actual SQLite checkpoint and completion survive SDK overlap; later checkpoint passes'),
    ('resume', 'writer_resume', [], 'app/Commands.lean',
     'w.paused.modify (fun _ => paused)', 'w.paused.set paused',
     'actual writer resumes and commits its queued valid op after the overlapping pause read',
     'writer-resume: actual writer commits valid queued ops after SDK overlap; deliberate pause remains effective'),
    ('prune', 'prune_ack', [], 'app/Commands.lean',
     'w.read.modify (fun _ => seq)', 'w.read.set seq',
     'actual prune step retains a concurrently published journal acknowledgement',
     'prune-ack: actual production prune step observes the published progress after SDK overlap'),
    ('reader-seen', 'prune_ack', ['--reader'], 'app/Screen.lean',
     'sh.seen.modify (fun _ => top)', 'sh.seen.set top',
     'actual reader pass publishes journal progress despite the overlapping old read',
     'reader-seen: actual reader pass publication survives SDK overlap and idle pass; real journal is pruned'),
]

def run(root, command, name, timeout):
    child = sp.Popen(command, cwd=root, text=True, stdout=sp.PIPE, stderr=sp.STDOUT,
                     start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except sp.TimeoutExpired:
        # Own only this command's session, including debugger/inferior children.
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (OUT / (name + '.log')).write_text(text + '\nTIMEOUT\n')
        raise
    (OUT / (name + '.log')).write_text(text)
    return child.returncode, text


def check(root, case, suffix, negative=False):
    name, target, args, _, _, _, failure, success = case
    label = name + '-' + suffix
    code, text = run(root, ['gdb', '-nx', '-q', '-batch', '-x', 'tests/engine/ref_publications.gdb',
        '--args', str(root / '.lake/build/bin' / target), str(OUT / (label + '-data'))] + args, label, 60)
    assert 'SDK getter paused before restoring its old value' in text and 'request entered=1' in text, text
    assert not any(marker in text for marker in ['SIGSEGV', 'SIGABRT', 'PANIC',
        'Error in sourced command file', 'uncaught exception', 'writer:']), text
    if negative:
        assert code == 1 and 'publication probe exit_group status=1' in text and \
            'completed while read paused=1' in text and 'FAIL: ' + failure in text, (code, text)
        if name == 'checkpoint':
            assert 'durable=true, queued=false, saved=0, requested=1, before=false, after=false, retry=false' in text, text
    else:
        assert code == 0 and 'publication probe exit_group status=0' in text and \
            'completed while read paused=0' in text and success in text, (code, text)


def build(root, target, name):
    code, _ = run(root, CAP + ['lake', 'build', target], name + '-build', 300)
    assert code == 0, f'{name}: mutant/restoration must compile, see {OUT}'


for case in CASES:
    check(ROOT, case, 'baseline')
with tempfile.TemporaryDirectory(prefix='ref-publications-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp) / 'base'
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
        'engine/renderer engine/sync app tests/engine',
        'publication-snapshot', str(scratch)], cwd=ROOT, check=True)

    def control(case, work):
        name, target, _, source, old, new, _, _ = case
        path = work / source
        original = path.read_text()
        assert original.count(old) == 1, f'{name}: ambiguous publication anchor'
        path.write_text(original.replace(old, new))
        build(work, target, name + '-direct-set')
        check(work, case, 'direct-set', True)
        return f'refused: {name} direct-set (compiled, real production effect and SDK overlap)'

    mutants.each(scratch, CASES, control)
print('publication gate: four real production/SQLite cases, four compiling controls, each in its own copy', flush=True)
