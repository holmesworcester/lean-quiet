#!/usr/bin/env python3
"""Actual connect/reader ownership and deterministic stop-token controls.

Linux x86-64, GDB/ptrace-child support, and the pinned Lean SDK are required.
Each mutation must compile and fail its exact assertion; signals, debugger
errors, missing breakpoints and build failures never count as a control.
"""
from pathlib import Path
import os
import re
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/native-lifetime'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']


def run(root, command, name, timeout=90):
    try:
        p = sp.run(command, cwd=root, text=True, stdout=sp.PIPE, stderr=sp.STDOUT, timeout=timeout)
    except sp.TimeoutExpired as e:
        output = e.stdout or b''
        if isinstance(output, bytes): output = output.decode(errors='replace')
        (OUT / (name + '.log')).write_text(output + '\nTIMEOUT\n')
        raise
    (OUT / (name + '.log')).write_text(p.stdout)
    return p.returncode, p.stdout


def build(root, name, target):
    code, text = run(root, CAP + ['lake', 'build', target], name + '-build', 300)
    assert code == 0, f'{name}: mutation must compile; see {OUT}'


def native(root, name, part=None, expected=None):
    args = [str(root / '.lake/build/bin/native_lifetime')]
    if part: args.append(part)
    code, text = run(root, args, name)
    assert not any(s in text.lower() for s in ['panic', 'uncaught exception', 'assertion violation',
                                              'segmentation fault', 'network runner stopped:']), text
    if expected:
        assert code == 1 and 'native-lifetime:' in text and f'FAIL: {expected}' in text, (name, code, text)
    else:
        assert code == 0 and 'native-lifetime: 26 passed, 0 failed' in text, (name, code, text)


def stopped(root, name, negative=False, reader=False):
    target = "reader_stop" if reader else "stop_flag"
    code, text = run(root, ['gdb', '-nx', '-q', '-batch', '-x', 'tests/engine/stop_flag.gdb',
                            '.lake/build/bin/' + target], name, 60)
    assert 'SDK getter paused before restoring its old value' in text, text
    assert 'request entered=1' in text, text
    assert not any(s in text for s in ['SIGSEGV', 'SIGABRT', 'PANIC', 'Error in sourced command file']), text
    failure = ('the actual reader stop publication survives the overlapping old read' if reader else
               'a completed stop request survives the overlapping old read')
    success = ('reader-stop: actual requestStop survives deterministic SDK overlap and repeated cancellation' if reader else
               'stop-flag: deterministic overlapping read/request and repeated stop pass')
    if negative:
        assert code == 1 and 'stop probe exit_group status=1' in text and 'completed while read paused=1' in text and \
            ('FAIL: ' + failure) in text, (name, code, text)
    else:
        assert code == 0 and 'stop probe exit_group status=0' in text and 'completed while read paused=0' in text and \
            success in text, (name, code, text)


native(ROOT, 'baseline')
stopped(ROOT, 'stop-baseline')
stopped(ROOT, 'reader-stop-baseline', reader=True)
with tempfile.TemporaryDirectory(prefix='native-lifetime-', dir=os.environ['TMPDIR']) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
            'engine/renderer engine/sync app tests/engine',
            'native-lifetime-snapshot', str(scratch)], cwd=ROOT, check=True)
    stop = scratch / 'engine/wire/StopFlag.lean'
    original = stop.read_text()
    cases = [
        ('unguarded-stop-read',
         'def StopFlag.get (flag : StopFlag) : IO Bool :=\n  flag.state.atomically (getThe Bool)',
         '@[extern "lq_stop_probe_bad_get"] private opaque badGet (state : @& Std.Mutex Bool) : IO Bool\n\n'
         'def StopFlag.get (flag : StopFlag) : IO Bool :=\n  badGet flag.state'),
        ('dropped-stop', 'flag.state.atomically (set true)', 'pure ()'),
    ]
    for name, old, new in cases:
        assert original.count(old) == 1, f'{name}: anchor changed'
        try:
            stop.write_text(original.replace(old, new))
            build(scratch, name, 'stop_flag')
            stopped(scratch, name, True)
            print(f'refused: {name} (compiled, exact SDK interleaving)', flush=True)
        finally:
            stop.write_text(original)
    build(scratch, 'stop-restored', 'stop_flag')
    stopped(scratch, 'stop-restored')
    reader = scratch / 'app/Screen.lean'
    original_reader = reader.read_text()
    old = 'w.stopped.modify (fun _ => true)'
    assert original_reader.count(old) == 1, 'reader stop helper anchor changed'
    try:
        reader.write_text(original_reader.replace(old, 'w.stopped.set true'))
        build(scratch, 'reader-lost-stop', 'reader_stop')
        stopped(scratch, 'reader-lost-stop', negative=True, reader=True)
        print('refused: reader-lost-stop (compiled, actual helper and SDK interleaving)', flush=True)
    finally:
        reader.write_text(original_reader)
    build(scratch, 'reader-stop-restored', 'reader_stop')
    stopped(scratch, 'reader-stop-restored', reader=True)
    cases = [
        ('release-quota-before-reader', 'engine/wire/Tcp.lean', '--reader-only',
         '  finally\n    cleanupReader\n    slots.release addr',
         '  finally\n    slots.release addr\n    cleanupReader',
         'native quota remains held while the original reader task exit is gated'),
        ('omit-reader-stop', 'engine/wire/Tcp.lean', '--reader-only',
         '  stopped.request\n  discard <| client.native.cancelRecv.toBaseIO',
         '  pure ()\n  discard <| client.native.cancelRecv.toBaseIO',
         'writer cleanup stops the actual backpressured reader body'),
        ('omit-production-reader-join', 'engine/wire/Tcp.lean', '--reader-only',
         '        (finishReader stopped c readerDone)', '        (pure ())',
         'production addSock writer stops and joins its original reader task'),
        ('no-connect-abort', 'engine/wire/SocketAbort.lean', '--connect-only',
         '        unless ← cap.abort do', '        unless true do',
         "actual Runner connect deadline releases the original native request's lease"),
        ('no-connect-deadline', 'engine/wire/Tcp.lean', '--connect-only',
         '(dialOut ch st.slots addr st.ingress.stopped cfg.stallMs)',
         '(dialOut ch st.slots addr st.ingress.stopped 86400000)',
         "actual Runner connect deadline releases the original native request's lease"),
        ('no-connect-stop', 'engine/wire/Tcp.lean', '--connect-only',
         '(dialOut ch st.slots addr st.ingress.stopped cfg.stallMs)',
         '(dialOut ch st.slots addr (pure false) cfg.stallMs)',
         'Runner.stop cancels native connect and releases quota without waiting 30 seconds'),
        ('lost-failed-completion-lease', 'engine/wire/Tcp.lean', '--connect-only',
         '    unless ← enqueue ch (.dialed addr none) cancel do slots.release addr',
         '    unless ← enqueue ch (.dialed addr none) cancel do pure ()',
         'dial task releases its own lease when stopped completion cannot enqueue'),
        ('lost-queued-failure-lease', 'engine/wire/Tcp.lean', '--connect-only',
         '    | .dialed addr none => slots.release addr',
         '    | .dialed addr none => pure ()',
         'stop drain releases an unhandled failed-dial completion exactly once'),
    ]
    for name, source, part, old, new, expected in cases:
        path = scratch / source
        original = path.read_text()
        assert original.count(old) == 1, f'{name}: anchor changed'
        try:
            path.write_text(original.replace(old, new))
            build(scratch, name, 'native_lifetime')
            native(scratch, name, part, expected)
            print(f'refused: {name} (compiled, intended runtime assertion)', flush=True)
        finally:
            path.write_text(original)
    build(scratch, 'restored', 'native_lifetime')
    native(scratch, 'restored')
print('native lifetimes: 26 checks, eight lifetime and three stop controls; restored suites pass', flush=True)
