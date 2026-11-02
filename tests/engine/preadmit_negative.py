#!/usr/bin/env python3
"""Mutation controls of the pre-admission room selection (docs/TAKE-ROOM.md).

In a scratch snapshot, each mutant restores a leak, and the build of the
laws must fail inside the named theorem (an error elsewhere, or a parse
or import error, is not a rejection). The snapshot is restored and must
build again. Logs stay in out/preadmit/controls.
"""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/preadmit/controls'
OUT.mkdir(parents=True, exist_ok=True)
CAP = ['systemd-run', '--user', '--scope', '-q', '-p', 'CPUWeight=1000', '-p', 'MemoryMax=16G', '-p', 'MemorySwapMax=0']


def run(root, command, name, timeout=1800):
    child = sp.Popen(command, cwd=root, text=True, stdout=sp.PIPE, stderr=sp.STDOUT,
                     start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except sp.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (OUT / (name + '.log')).write_text(text + '\nTIMEOUT\n')
        raise
    (OUT / (name + '.log')).write_text(text)
    return child.returncode, text


def spans(source, names):
    """Line ranges [first, last) of these theorems in a source."""
    out = {}
    for n in names:
        begin = source.index('theorem ' + n + ' ')
        end = source.find('\ntheorem ', begin + 1)
        end = len(source) if end < 0 else end
        out[n] = (source[:begin].count('\n') + 1, source[:end].count('\n') + 1)
    return out


# (name, file mutated, anchor, mutant, target, file of the laws, the theorem
#  that must reject it, every theorem an error may fall in)
CASES = [
    ('full-room', 'app/Commands.lean',
     '    if ← ((linked c me peer).liftL : View F Bool) then return [Room.take c]',
     '    if ← ((linked c me peer).liftL : View F Bool) then return [Room.sync c]',
     'app.Proofs', 'app/Proofs.lean', 'roomFor_law', ['roomFor_law', 'eval_roomFor']),
    ('unlive-notices', 'app/Commands.lean',
     '  let cut ← if live then pure xs else ((Community.cutBy c).liftL : View F (List Id))',
     '  let cut ← pure xs',
     'app.Proofs', 'app/Proofs.lean', 'mem_noticesFor', ['mem_noticesFor', 'notice_mem_noticesFor']),
    ('cut-entries-silent', 'app/Commands.lean',
     '  | none => noticesFor gave c peer false',
     '  | none => return []',
     'app.Proofs', 'app/Proofs.lean', 'cut_notifies', ['cut_notifies', 'eval_roomFor', 'roomFor_law']),
    ('take-room-opens-from-index', 'engine/sync/Conn.lean',
     'def Conn.view (ix : Index) (c : Conn) (r : Id) : Index := if has c.rooms r then ix else {}',
     'def Conn.view (ix : Index) (c : Conn) (r : Id) : Index := if has c.rooms r then ix else ix',
     'engine.sync.Conn', 'engine/sync/Conn.lean', 'Conn.view_items', ['Conn.view_items']),
    ('take-room-wants-blind', 'engine/sync/Conn.lean',
     '  if has c.rooms r then ix.answer P r f cl else answerTake P cl',
     '  if has c.rooms r then ix.answer P r f cl else ({} : Index).answer P r f cl',
     'engine.sync.Conn', 'engine/sync/Conn.lean', 'Conn.answer_blank', ['Conn.answer_blank']),
]

import sys
if sys.argv[1:]:
    assert set(sys.argv[1:]) <= {c[0] for c in CASES}, 'unknown mutant'
    CASES = [c for c in CASES if c[0] in sys.argv[1:]]

with tempfile.TemporaryDirectory(prefix='preadmit-', dir=os.environ.get('TMPDIR')) as temp:
    scratch = Path(temp)
    sp.run(['bash', '-c', '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire engine/sync '
            'engine/world engine/renderer app', 'preadmit-snapshot', str(scratch)], cwd=ROOT, check=True)
    code, text = run(scratch, CAP + ['lake', 'build', 'app.Proofs', 'engine.sync.TakeLaws'], 'baseline')
    assert code == 0, 'baseline does not build'
    for name, file, old, new, target, laws, named, allowed in CASES:
        source = scratch / file
        original = source.read_text()
        assert original.count(old) == 1, f'{name}: ambiguous mutation anchor'
        law_source = (scratch / laws).read_text()
        where = spans(law_source if laws != file else original, allowed)
        try:
            source.write_text(original.replace(old, new))
            code, text = run(scratch, CAP + ['lake', 'build', target], name)
            assert code != 0, f'{name}: the mutant built'
            for marker in ['unknown identifier', 'Unknown identifier', 'unexpected token', 'unknown module',
                           'failed to read', 'unable to load', 'object file']:
                assert marker not in text, f'{name}: not a proof rejection: {marker}'
            errors = [(f, int(n)) for f, n in re.findall(r'^error: ([^\s:]+):(\d+):\d+:', text, re.M)]
            assert errors, f'{name}: no located error'
            for f, n in errors:
                assert f == laws and any(a <= n < b for a, b in where.values()), \
                    f'{name}: error outside the named theorems: {f}:{n}'
            a, b = where[named]
            assert any(a <= n < b for _, n in errors), f'{name}: {named} does not reject it'
            print(f'rejected {name} by {named}', flush=True)
        finally:
            source.write_text(original)
    code, text = run(scratch, CAP + ['lake', 'build', 'app.Proofs', 'engine.sync.TakeLaws'], 'restored')
    assert code == 0, 'restored snapshot does not build'
print(f'preadmit: {len(CASES)} mutants rejected by their laws, restored pass', flush=True)
