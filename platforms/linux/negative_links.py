#!/usr/bin/env python3
"""The Linux shell's link delivery, broken three ways; each must fail the
links e2e (platforms/linux/links.sh) on the check it is there for. The source
is restored after each, and the shell rebuilt."""
import os
from pathlib import Path
import subprocess as sp

root = Path(__file__).resolve().parents[2]
shell = root / 'platforms/linux/shell.c'
out = root / 'out/desktop/negative'
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.setdefault('ELAN_HOME', '/mnt/storage/elan')
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']


def old_links(source):
    """lq_links as it was: links dropped."""
    start = source.index('lean_obj_res lq_links(void) {')
    end = source.index('\n}\n', start) + 3
    return source[:start] + 'lean_obj_res lq_links(void) { return lean_io_result_mk_ok(lean_mk_empty_array()); }\n' + source[end:]


def edit(old, new):
    def apply(source):
        assert source.count(old) == 1, old
        return source.replace(old, new)
    return apply


for name, mutate, expected in [
    ('empty-links', old_links, 'timeout: cold start: the app takes the link in its arguments'),
    # every database named alike: one socket for all of them
    ('one-socket', edit('    for (const char *p = path; *p; p++) h = (h ^ (unsigned char)*p) * 1099511628211ull;\n', ''),
     'timeout: a second database gets its own instance'),
    # links taken, the window never raised
    ('no-raise', edit('if (links.raise && q.c) {', 'if (false && links.raise && q.c) {'),
     'timeout: warm xdg-open: _NET_ACTIVE_WINDOW'),
]:
    original = shell.read_text()
    try:
        shell.write_text(mutate(original))
        p = sp.run(['bash', 'platforms/linux/links.sh'], cwd=root, env=env, stdout=sp.PIPE, stderr=sp.STDOUT,
                   text=True, timeout=900)
        (out / (name + '-links.log')).write_text(p.stdout)
        assert p.returncode != 0 and expected in p.stdout, f'{name}: not refused; see {out / (name + "-links.log")}'
        print('rejected', name, flush=True)
    finally:
        shell.write_text(original)
p = sp.run(['bash', 'platforms/linux/build.sh'], cwd=root, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True,
           timeout=900)
assert p.returncode == 0, p.stdout
print('negative controls: 3 link mutations rejected; source restored and the shell rebuilt')
