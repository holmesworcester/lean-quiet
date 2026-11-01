#!/usr/bin/env python3
"""Actual helper/decoder checks with compiling, assertion-specific controls.

This deterministic component gate is separate from the provisioned Android
App/JNI/SQLite gate. Run its shell wrapper to retain the 48 GiB process scope.
"""
from pathlib import Path
import os
import subprocess
import tempfile
import shutil

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out' / 'owned-input-core'
OUT.mkdir(parents=True, exist_ok=True)


def run(name, args, *, cwd=ROOT, env=None, code=0, assertion=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=120)
    (OUT / (name + '.log')).write_text(result.stdout)
    if result.returncode != code or (assertion and assertion not in result.stdout):
        raise RuntimeError(f'{name}: exit {result.returncode}, expected {code}; '
                           f'assertion={assertion!r}\n{result.stdout[-5000:]}')
    print(f'{name}: passed', flush=True)
    return result.stdout


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'control anchor changed: {old!r}')
    return text.replace(old, new)


def c_check(name, header, control=False, assertion=None):
    with tempfile.TemporaryDirectory(prefix='owned-input-c-', dir=os.environ['TMPDIR']) as tmp:
        tmp = Path(tmp)
        (tmp / 'test').mkdir()
        (tmp / 'editor_action.h').write_text(header)
        (tmp / 'test' / 'editor_action.c').write_text(
            (ROOT / 'platforms/native/test/editor_action.c').read_text())
        exe = tmp / 'test' / 'editor_action'
        run(name + '-compile', ['cc', '-std=c11', '-Wall', '-Wextra', '-Werror', '-O2',
                                str(tmp / 'test/editor_action.c'), '-o', str(exe)])
        run(name, [str(exe)], code=1 if control else 0, assertion=assertion)


header = (ROOT / 'platforms/native/editor_action.h').read_text()
c_check('native-baseline', header, assertion='editor-action: 30 passed, 0 failed')
c_check('native-consumption-control', replace_once(header,
    'free(s->text);s->text=NULL;',
    's->consumed_owner=0;s->consumed_revision=0;free(s->text);s->text=NULL;'), True,
    'FAIL editor-action: consumed text cannot resurrect after clear completion')
c_check('native-copy-failure-control', replace_once(header,
    'if(!copy)return LQ_ACTION_MEMORY;',
    'if(!copy){copy=malloc(n+1);if(!copy)abort();memset(copy,0,n+1);}'), True,
    'FAIL editor-action: admission allocation failure explicitly refuses without consuming ticket')
c_check('native-clear-ticket-control', replace_once(header,
    'if(ticket&&s->ticket==ticket&&s->clearing)',
    'if(ticket&&s->clearing)'), True,
    'FAIL editor-action: unrelated completion cannot release clear')
c_check('native-consumed-readmit-control', replace_once(header,
    '  if(lq_action_consumed(s,owner,revision))return LQ_ACTION_STALE;',''), True,
    'FAIL editor-action: consumed raw text cannot be readmitted after failed clear')
c_check('native-restored', header, assertion='editor-action: 30 passed, 0 failed')

lake = str(Path(os.environ['ELAN_HOME']) / 'bin/lake')
lean = run('lean-path', [lake, 'env', 'which', 'lean']).strip()
path = run('lean-search-path', [lake, 'env', 'printenv', 'LEAN_PATH']).strip()
path = ':'.join(str((ROOT / p).resolve()) if not Path(p).is_absolute() else p
                for p in path.split(':') if p)
base_env = dict(os.environ, LEAN_PATH=path)
test = ROOT / 'tests/engine/OwnedInput.lean'
run('decoder-compile', [lean, str(test)], env=base_env)
run('decoder-baseline', [lean, '--run', str(test)], env=base_env,
    assertion='owned-input: 22 passed, 0 failed')
source = (ROOT / 'engine/renderer/Input.lean').read_text()
controls = [
    ('orphan-cleanup',
     'if let some (t, o, _) := pending then out := out.push (.event (.action t o 2 []))\n  return out.toList',
     'return out.toList',
     'FAIL owned-input: orphan envelope remains an explicit cleanup envelope'),
    ('held-owner',
     '| .touch _ | .touchOn _ _ | .touchAt _ _ _ => (s.press.map (·.context.editor)).getD 0',
     '| .touch _ | .touchOn _ _ | .touchAt _ _ _ => admitted',
     'FAIL owned-input: ignored Up still has one exact cleanup token'),
]
for name, old, new, assertion in controls:
    with tempfile.TemporaryDirectory(prefix='owned-input-lean-', dir=os.environ['TMPDIR']) as tmp:
        tmp = Path(tmp)
        shutil.copytree(ROOT / '.lake/build/lib/lean', tmp,
                        copy_function=os.symlink, dirs_exist_ok=True)
        rel = Path('engine/renderer/Input.lean')
        for artifact in (tmp / rel).parent.glob('Input.*'):
            if artifact.is_symlink():
                artifact.unlink()
        (tmp / rel).write_text(replace_once(source, old, new))
        env = dict(base_env, LEAN_PATH=str(tmp) + ':' + path)
        run(name + '-compile', [lean, '-o', str(rel.with_suffix('.olean')), str(rel)],
            cwd=tmp, env=env)
        run(name + '-test-compile', [lean, str(test)], env=env)
        run(name, [lean, '--run', str(test)], env=env, code=1, assertion=assertion)
run('decoder-restored', [lean, '--run', str(test)], env=base_env,
    assertion='owned-input: 22 passed, 0 failed')
print('owned-input core: baseline, 6 compiling controls, restored passed', flush=True)
