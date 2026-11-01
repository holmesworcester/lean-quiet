#!/usr/bin/env python3
"""Compiled controls of the shared production desktop publication path.
Each runtime failure must be exit 1 and the intended assertion, not a build
error, timeout, or signal. Isolated snapshots preserve the working tree.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/desktop-presentation/negative'
OUT.mkdir(parents=True, exist_ok=True)
CASES = [
    ('staging-completes', 'platforms/desktop/Driver.lean', 'return Publication.staged id', 'return #[]',
     'desktop App layer staging never acknowledges an unpresented committed own send'),
    ('replace-delayed', 'platforms/desktop/Presentation.lean',
     'if prior.any (fun p => result.tracking == some p.frame) || result.tracking.isNone\n      then prior else candidate', 'candidate',
     'five newer App staging frames cannot replace a delayed accepted desktop candidate'),
    ('ignore-shift', 'platforms/desktop/Presentation.lean',
     '((result.completed.filter fun r => r.2 == 0).map Prod.fst)', '(result.completed.map Prod.fst)',
     'a completed desktop frame translated away from the content does not acknowledge it'),
    ('replace-tracked-redraw', 'platforms/desktop/Presentation.lean',
     'if prior.any (fun p => result.tracking == some p.frame) || result.tracking.isNone',
     'if result.tracking.isNone',
     'accepted newer redraw keeps its input while an older completion is tracked'),
    ('stale-pointer', 'platforms/desktop/Publication.lean',
     'if r.accepted then return r.events', 'if true then return r.events',
     'refused geometry drops stale pointer actions, keeps text keys and close, and cancels gestures'),
    ('ignore-covered-body', 'platforms/desktop/Presentation.lean',
     'if bodyMatches d.app row bodyY body\n          ((picture.rows.extract y (y + body.size)).map fun r => r.extract x (x + d.app.W * 4))',
     'if true', 'an opaque overlay over the actual text cannot acknowledge presentation'),
    ('refuse-preview', 'platforms/desktop/Presentation.lean',
     'if bodyY == box.y then\n      return box.w > 0',
     'if bodyY == box.y then\n      return false && box.w > 0',
     'a desktop photo-only send acknowledges its actual decoded preview rectangle'),
    ('ignore-hover-paint', 'platforms/desktop/Presentation.lean',
     '(rendered.filter (fun r => r.1 == p.message)).map Prod.snd <|> row.shown', 'row.shown',
     'actual desktop hover styling still acknowledges its visible committed body'),
    ('ignore-popup', 'platforms/desktop/Presentation.lean',
     'if d.ui.switching || d.ui.context != .closed then none else do', 'if false then none else do',
     'an overlaid desktop popup cannot acknowledge the inactive conversation'),
]
if sys.argv[1:]:
    names = set(sys.argv[1:])
    assert names <= {c[0] for c in CASES}, 'unknown control'
    CASES = [c for c in CASES if c[0] in names]

def no_runtime_crash(text):
    return not any(marker in text.lower() for marker in ["panic", "uncaught exception", "segmentation fault", "assertion violation"])

def run(args, cwd, name, timeout=180):
    log = OUT / (name + '.log')
    with log.open('w') as out:
        p = subprocess.run(args, cwd=cwd, stdout=out, stderr=subprocess.STDOUT, timeout=timeout)
    return p.returncode, log.read_text()

with tempfile.TemporaryDirectory(prefix='quiet-desktop-controls-', dir=os.environ.get('TMPDIR', '/mnt/storage/holmes-tmp')) as folder:
    work = Path(folder) / 'work'
    shutil.copytree(ROOT, work, symlinks=True,
        ignore=shutil.ignore_patterns('.git', 'out', '__pycache__'))
    for name, file, old, new, expected in CASES:
        path = work / file
        source = path.read_text()
        assert source.count(old) == 1, (name, 'anchor')
        try:
            path.write_text(source.replace(old, new))
            code, text = run(['lake', 'build', 'desktop_presentation'], work, name + '-build')
            assert code == 0, (name, 'must compile', text[-2000:])
            code, text = run([str(work / '.lake/build/bin/desktop_presentation')], work, name)
            assert code == 1 and ('FAIL: ' + expected) in text and no_runtime_crash(text), (name, code, text[-3000:])
            print('rejected', name, flush=True)
        finally:
            path.write_text(source)
    code, text = run(['lake', 'build', 'desktop_presentation'], work, 'restored-build')
    assert code == 0, text[-2000:]
    code, text = run([str(work / '.lake/build/bin/desktop_presentation')], work, 'restored')
    assert code == 0 and '20 passed, 0 failed' in text and no_runtime_crash(text), text
    print(text, end='')
