#!/usr/bin/env python3
"""Emit the shared desktop's exact C closure using the pinned host Lean."""
import os, pathlib, re, shutil, subprocess
root = pathlib.Path(__file__).resolve().parents[2]
os.chdir(root)
os.environ.setdefault('ELAN_HOME', '/mnt/storage/elan')
os.environ.setdefault('TMPDIR', '/mnt/storage/holmes-tmp')
lake = pathlib.Path(os.environ['ELAN_HOME']) / 'bin/lake'
seen, order = set(), []
def visit(m):
    if m in seen or m.split('.')[0] in ('Init', 'Std', 'Lean'): return
    seen.add(m)
    p = root / (m.replace('.', '/') + '.lean')
    for dep in re.findall(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)', p.read_text(), re.M): visit(dep)
    order.append(m)
main = os.environ.get('WINDOWS_MAIN', 'platforms.windows.Main')
visit(main)
subprocess.run([str(lake), 'build', *('+' + m + ':c' for m in order)], check=True)
st = root / 'out/windows/stage'
(st/'ir').mkdir(parents=True, exist_ok=True)
for m in order:
    shutil.copy2(root / '.lake/build/ir' / (m.replace('.', '/') + '.c'), st/'ir'/f'{m}.c')
(st/(os.environ.get('WINDOWS_SOURCES', 'sources.txt'))).write_text('\n'.join(f'ir/{m}.c' for m in order)+'\n')
for folder in ('assets', 'platforms/windows', 'platforms/native', 'engine/native', 'third_party/sqlite'):
    dest = st / {'platforms/windows':'windows','platforms/native':'native','engine/native':'glue','third_party/sqlite':'sqlite'}.get(folder,folder)
    shutil.copytree(root/folder, dest, dirs_exist_ok=True, ignore=shutil.ignore_patterns('target', '.git'))
print(st)
