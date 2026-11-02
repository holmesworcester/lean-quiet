#!/usr/bin/env python3
"""Keep the real admitted frame; reject compiling teardown/admission controls."""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/close-ingress'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']


def run(root, args, name, timeout=600):
    child = sp.Popen(args, cwd=root, text=True, stdout=sp.PIPE, stderr=sp.STDOUT, start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except sp.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (OUT / (name + '.log')).write_text(text + '\nTIMEOUT\n')
        raise
    (OUT / (name + '.log')).write_text(text)
    return child.returncode, text


def build(root, name, target='close_ingress', succeeds=True):
    code, text = run(root, CAP + ['lake', 'build', target], name + '-build')
    if succeeds:
        assert code == 0, f'{name}: compilation failure is not a successful control'
    else:
        assert code > 0 and 'error: engine/wire/IngressFreezeLaws.lean:' in text, text
        assert not any(x in text.lower() for x in ['unknown module', 'unknown constant', 'sorry', 'panic']), text


ALLOWED = {
    'freeze captures exactly the already admitted value',
    'freeze cancels a backpressured producer without consuming its frame',
    'frozen producer receives explicit refusal',
    'flood after freeze cannot refill or replace the single owed frame',
    'frozen source keeps its ownership and cannot be reused',
    'normal poll still selects the original frozen value',
    'repeated freeze cannot create another owed value',
    'retirement reuses the bounded source after frozen consumption',
    'stale freeze cannot seal a replacement incarnation',
    'invalid captured input retains keys for exactly one real handler',
    'invalid frame refusal still closes and erases keys in its selected handler',
    'local removal starts with exactly one frozen transport obligation',
    'authenticated local removal immediately bypasses transport frame retention',
}
for label in ['SQLite error', 'notification error']:
    ALLOWED.update(label + ' ' + suffix for suffix in [
        'starts with one frozen valid frame and live session',
        'reports the original selected-handler failure',
        'releases frozen native source even when close-time SQL can fail'])
ALLOWED.add('post-commit notification failure still applies input and erases the session')
for prefix in ['closed', 'reap']:
    ALLOWED.update(prefix + ' ' + suffix for suffix in [
        'retains admitted notice and session keys ahead of transport teardown',
        'refuses all later source input without releasing ownership',
        'local write completes while same-turn tick and expiry preserve owed input',
        'actual loop applies retained authenticated notice within its source bound',
        'selected notice closes immediately and grants no second input grace'])


def check(root, name, expected=None):
    data = tempfile.mkdtemp(prefix=name + '-data-', dir=OUT)
    code, text = run(root, [str(root / '.lake/build/bin/close_ingress'), data], name, 900)
    assert not any(x in text.lower() for x in ['panic', 'uncaught exception', 'segmentation fault', 'error:']), text
    failures = set(re.findall(r'^FAIL: (.+)$', text, re.M))
    if expected:
        assert code == 1 and 'close-ingress:' in text and expected in failures, (code, text)
        assert failures <= ALLOWED, f'{name}: unrelated failures {failures - ALLOWED}'
        print(f'refused: {name} (compiled; {len(failures)} specific assertions)', flush=True)
    else:
        assert code == 0 and 'close-ingress: 40 passed, 0 failed' in text, (code, text)
        print(text, end='', flush=True)


def edit(path, old, new):
    text = path.read_text()
    assert text.count(old) == 1, f'missing/ambiguous mutation anchor in {path}'
    path.write_text(text.replace(old, new))


check(ROOT, 'baseline')
with tempfile.TemporaryDirectory(prefix='close-ingress-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
        'engine/renderer engine/sync app tests/engine', 'close-ingress-snapshot', str(scratch)], cwd=ROOT, check=True)
    tcp = scratch / 'engine/wire/Tcp.lean'
    hub = scratch / 'engine/wire/IngressIO.lean'
    originals = {path: path.read_text() for path in [tcp, hub]}
    cases = [
        ('old-control-close', tcp,
         '| .closed sid => return some (← st.transportClosed x ch notify cfg sid now)',
         '| .closed sid => return some (← st.closeApply x ch notify cfg sid now)',
         'closed retains admitted notice and session keys ahead of transport teardown'),
        ('old-reap-close', tcp,
         'if ← IO.hasFinished s.done then st ← st.transportClosed x ch notify cfg s.id now',
         'if ← IO.hasFinished s.done then st ← st.closeApply x ch notify cfg s.id now',
         'reap retains admitted notice and session keys ahead of transport teardown'),
        ('refill-frozen', hub,
         'if r.closed || !r.live[source] || !r.accepting[source] then',
         'if r.closed || !r.live[source] then',
         'freeze cancels a backpressured producer without consuming its frame'),
        ('missing-post-frame-close', tcp,
         'if s.closeAfterFrame then return some (← st.closeApply x ch notify cfg sid now)',
         'if false then return some (← st.closeApply x ch notify cfg sid now)',
         'invalid frame refusal still closes and erases keys in its selected handler'),
        ('missing-session-deferral', tcp,
         'if protect || (st.node.addr? cid).any closing.contains then deferred := cid :: deferred',
         'if protect then deferred := cid :: deferred',
         'closed local write completes while same-turn tick and expiry preserve owed input'),
        ('missing-socket-deferral', tcp,
         'if s.closeAfterFrame then continue', 'if false then continue',
         'closed local write completes while same-turn tick and expiry preserve owed input'),
        ('missing-error-cleanup', tcp,
         'if s.closeAfterFrame then st.failedFrame x ch notify cfg s now',
         'if false then st.failedFrame x ch notify cfg s now',
         'SQLite error releases frozen native source even when close-time SQL can fail'),
        ('missing-error-session-close', tcp,
         'try discard <| st.closeApply x ch notify cfg s.id now',
         'try if false then discard <| st.closeApply x ch notify cfg s.id now',
         'post-commit notification failure still applies input and erases the session'),
        ('early-source-reuse', hub,
         '{ r with accepting := r.accepting.set source.val false }',
         '{ r with accepting := r.accepting.set source.val false, live := r.live.set source.val false }',
         'frozen source keeps its ownership and cannot be reused'),
    ]
    for name, path, old, new, expected in cases:
        try:
            edit(path, old, new)
            build(scratch, name)
            check(scratch, name, expected)
        finally:
            for path, text in originals.items(): path.write_text(text)
    try:
        edit(hub, '{ r with accepting := r.accepting.set source.val false }',
             '{ r with accepting := r.accepting.set source.val false, state := r.state.cancel source }')
        build(scratch, 'discard-admitted-kernel', 'engine.wire.IngressFreezeLaws', succeeds=False)
        print('refused: discard-admitted-kernel (unchanged IngressFreezeLaws)', flush=True)
    finally:
        for path, text in originals.items(): path.write_text(text)
    build(scratch, 'restored')
    check(scratch, 'restored')
