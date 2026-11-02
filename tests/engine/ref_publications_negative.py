#!/usr/bin/env python3
"""Production publication operations, real SQLite effects, exact SDK overlap.
Each case pauses the actual SDK getter and publishes through the running
production operation; the publication must survive. Lean 4.35.0's runtime
no longer loses an IO.Ref set to an overlapping get, so the old direct-set
mutants no longer fail and are not run (docs/REF-PUBLICATIONS.md).
"""
from pathlib import Path
import os
import signal
import subprocess as sp

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/ref-publications'
OUT.mkdir(parents=True, exist_ok=True)
CASES = [
    ('checkpoint', 'checkpoint_ack', [],
     'checkpoint-ack: actual SQLite checkpoint and completion survive SDK overlap; later checkpoint passes'),
    ('resume', 'writer_resume', [],
     'writer-resume: actual writer commits valid queued ops after SDK overlap; deliberate pause remains effective'),
    ('prune', 'prune_ack', [],
     'prune-ack: actual production prune step observes the published progress after SDK overlap'),
    ('reader-seen', 'prune_ack', ['--reader'],
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


def check(root, case, suffix):
    name, target, args, success = case
    label = name + '-' + suffix
    code, text = run(root, ['gdb', '-nx', '-q', '-batch', '-x', 'tests/engine/ref_publications.gdb',
        '--args', str(root / '.lake/build/bin' / target), str(OUT / (label + '-data'))] + args, label, 60)
    assert 'SDK getter paused before restoring its old value' in text and 'request entered=1' in text, text
    assert not any(marker in text for marker in ['SIGSEGV', 'SIGABRT', 'PANIC',
        'Error in sourced command file', 'uncaught exception', 'writer:']), text
    assert code == 0 and 'publication probe exit_group status=0' in text and \
        'completed while read paused=0' in text and success in text, (code, text)


for case in CASES:
    check(ROOT, case, 'baseline')
print('publication gate: four real production/SQLite cases pass under forced SDK overlap', flush=True)
