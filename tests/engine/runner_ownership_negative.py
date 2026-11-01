#!/usr/bin/env python3
"""Actual Runner native ownership: strict compiling controls and restored run."""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/runner-ownership'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']
ALLOWED = set(re.findall(r't\.ok "([^"]+)"', (ROOT / 'tests/engine/RunnerOwnership.lean').read_text()))


def run(root, args, name, timeout=180, stderr_full=False):
    with open('/dev/full', 'w') if stderr_full else open(os.devnull, 'w') as sink:
        child = sp.Popen(args, cwd=root, text=True, stdout=sp.PIPE,
                         stderr=sink if stderr_full else sp.STDOUT, start_new_session=True)
        try:
            output, _ = child.communicate(timeout=timeout)
        except sp.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            output, _ = child.communicate()
            (OUT / (name + '.log')).write_text(output + '\nTIMEOUT\n')
            raise
    (OUT / (name + '.log')).write_text(output)
    return child.returncode, output


def build(root, name, target='runner_ownership', success=True):
    code, text = run(root, CAP + ['lake', 'build', target], name + '-build', 600)
    if success:
        assert code == 0, f'{name}: compilation failure is not a valid control'
    else:
        assert code > 0 and 'error: engine/wire/JobOwnersLaws.lean:' in text, text
        assert not any(s in text.lower() for s in ['unknown module', 'unknown constant', 'sorry', 'panic']), text


def check(root, name, mode=None, expected=None, stderr_full=False):
    args = [str(root / '.lake/build/bin/runner_ownership')]
    if mode: args.append(mode)
    code, text = run(root, args, name, 35, stderr_full)
    assert code in [0, 1], (name, code, text)
    assert not any(s in text.lower() for s in ['panic', 'uncaught exception', 'segmentation fault']), text
    for line in text.splitlines():
        if 'network runner stopped:' in line:
            assert line == 'network runner stopped: expected RunnerOwnership tick failure', line
    failures = set(re.findall(r'^FAIL: (.+)$', text, re.M))
    assert failures <= ALLOWED, failures - ALLOWED
    if expected:
        assert code == 1 and expected in failures and 'runner-ownership:' in text, (name, code, text)
        print(f'refused: {name} (compiled, exact assertion)', flush=True)
    else:
        count = {'failure': 11, 'handoff': 4, 'retiring': 7, 'refused': 2, None: 24}[mode]
        assert code == 0 and f'runner-ownership: {count} passed, 0 failed' in text, (name, code, text)
        print(text, end='', flush=True)


check(ROOT, 'baseline')
check(ROOT, 'stderr-full-baseline', 'failure', stderr_full=True)
with tempfile.TemporaryDirectory(prefix='runner-ownership-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire engine/sync '
            'engine/renderer tests/engine', 'ownership-snapshot', str(scratch)], cwd=ROOT, check=True)
    job = scratch / 'engine/wire/JobOwners.lean'
    tcp = scratch / 'engine/wire/Tcp.lean'
    originals = {job: job.read_text(), tcp: tcp.read_text()}
    cases = [
        ('forgotten-jobs', job, 'set (job :: retained)', 'set retained', 'failure',
         'loop exception requests native cancellation without waiting for Runner.stop'),
        ('overwrite-earlier-job', job, 'set (job :: retained)', 'set [job]', 'failure',
         'failed-runner stop closes the previously completed peer'),
        ('no-cancellation-request', job, 'for j in jobs do discard <| j.cancel.toBaseIO',
         'for _ in jobs do pure ()', 'failure',
         'loop exception requests native cancellation without waiting for Runner.stop'),
        ('forget-unfinished-jobs', job,
         '(← getThe (List NativeJob)).filterM fun j => return !(← IO.hasFinished j.done)',
         'pure ([] : List NativeJob)', 'retiring',
         'full ownership table refuses before creating a new worker'),
        ('single-handoff-slot', job, ': Nat := 2 * maxSocks', ': Nat := maxSocks', 'handoff',
         'actual successful dial handoff admits socket before original dial task completes'),
        ('discard-retiring-notice', tcp,
         'if o.draining then o else { o with stopped := true, lanes := {}, control := {}, retry := .vacant }',
         'if false then o else { o with stopped := true, lanes := {}, control := {}, retry := .vacant }', 'retiring',
         'owned retirement still sends the exact final notice before EOF'),
        ('early-original-join', job, 'for j in jobs do discard <| IO.wait j.done',
         'for _ in jobs do pure ()', 'retiring',
         'cleanup retains a retired original writer until its native work finishes'),
        ('missing-automatic-teardown', tcp,
         'cleanupRunner ingress owners listening srv.native slots ch', 'pure ()', 'failure',
         'Runner.stop releases both old and same-turn native socket leases'),
        ('unbounded-worker-admission', job, ': Bool := jobs.length < cap', ': Bool := true', 'refused',
         'actual addSock refusal releases quota and source without retaining a socket'),
        ('diagnostic-replaces-original-error', tcp,
         'discard <| (IO.eprintln s!"network runner stopped: {e}").toBaseIO',
         'IO.eprintln s!"network runner stopped: {e}"', 'failure',
         'runner reports its original tick error without completing the failed turn'),
    ]
    for name, path, old, new, mode, expected in cases:
        try:
            assert originals[path].count(old) == 1, f'{name}: missing or ambiguous anchor'
            path.write_text(originals[path].replace(old, new))
            build(scratch, name)
            check(scratch, name, mode, expected, name == 'diagnostic-replaces-original-error')
        finally:
            for path, text in originals.items(): path.write_text(text)
    try:
        job.write_text(originals[job].replace(': Bool := jobs.length < cap', ': Bool := true'))
        build(scratch, 'unbounded-admission-kernel', 'engine.wire.JobOwnersLaws', False)
        print('refused: unbounded-admission-kernel (unchanged actual gate laws)', flush=True)
    finally:
        for path, text in originals.items(): path.write_text(text)
    build(scratch, 'restored')
    check(scratch, 'restored')
    check(scratch, 'stderr-full-restored', 'failure', stderr_full=True)
print('runner ownership: 24 checks, 10 runtime controls, 1 kernel control, restored', flush=True)
