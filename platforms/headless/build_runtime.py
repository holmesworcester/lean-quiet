#!/usr/bin/env python3
"""Build the phone runtime options for Linux, then the engine suites.

All generated C, including Init and Std, is compiled against the new
headers. Nothing links a prebuilt Lean runtime or allocator. Outputs and
command logs stay under out/phone-runtime; no toolchain files are changed.
"""
import concurrent.futures
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/phone-runtime'
ELAN = Path(os.environ.get('ELAN_HOME', '/mnt/storage/elan'))
LEAN = Path(subprocess.check_output([ELAN / 'bin/lean', '--print-prefix'], cwd=ROOT, text=True).strip())
SRC = Path(os.environ.get('LEAN_SRC', '/mnt/storage/holmes-wt/lean-src/lean4')) / 'src'
UV = Path(os.environ.get('UV_SRC', '/mnt/storage/holmes-wt/lean-src/libuv'))
CC = os.environ.get('CC', 'clang')
CXX = os.environ.get('CXX', 'clang++')
JOBS = int(os.environ.get('JOBS', '8'))
OUT.mkdir(parents=True, exist_ok=True)


def run(args, log, cwd=ROOT):
    args = list(map(str, args))
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('w') as f:
        print(' '.join(args), file=f, flush=True)
        subprocess.run(args, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, check=True)


def parallel(fn, items):
    with concurrent.futures.ThreadPoolExecutor(JOBS) as pool:
        list(pool.map(fn, items))


def sources(name):
    return (ROOT / 'platforms/leanrt' / name).read_text().split()


# Match the phone build's config, and reject a source/toolchain mismatch.
version = re.search(r'LEAN_VERSION_STRING "([^"]+)"', (LEAN / 'include/lean/version.h').read_text())[1]
src_version = (SRC / 'CMakeLists.txt').read_text()
for part, value in zip(('MAJOR', 'MINOR', 'PATCH'), version.split('.')[:3]):
    assert re.search(rf'set\(LEAN_VERSION_{part}\s+{value}\s', src_version), 'Lean source version mismatch'
assert '1.51.0' == '.'.join(re.search(rf'#define UV_VERSION_{p}\s+(\d+)', (UV / 'include/uv/version.h').read_text())[1]
                            for p in ('MAJOR', 'MINOR', 'PATCH')), 'libuv version mismatch'
inc = OUT / 'include'
shutil.copytree(LEAN / 'include/lean', inc / 'lean', dirs_exist_ok=True)
config = inc / 'lean/config.h'
config.write_text(config.read_text().replace('#define LEAN_MIMALLOC', ''))
(inc / 'githash.h').write_text('#define LEAN_GITHASH ""\n')
headers = hashlib.sha256()
for directory in (inc, SRC / 'runtime', SRC / 'util', UV / 'include'):
    for h in sorted(directory.rglob('*.h')):
        headers.update(h.read_bytes())
header_hash = headers.hexdigest()


def compile_one(item):
    src, obj, compiler, flags = item
    cmd = [compiler, *flags, '-c', str(src), '-o', str(obj)]
    digest = hashlib.sha256(src.read_bytes() + repr(cmd).encode() + header_hash.encode()).hexdigest()
    stamp = obj.with_suffix('.sha')
    if obj.exists() and stamp.exists() and stamp.read_text() == digest:
        return
    obj.parent.mkdir(parents=True, exist_ok=True)
    run(cmd, obj.with_suffix('.log'))
    stamp.write_text(digest)


def archive(name, objects):
    dest = OUT / name
    dest.unlink(missing_ok=True)
    run(['ar', 'rcs', dest, *objects], dest.with_suffix('.log'))


flags = ['-O3', '-fPIC', '-ffunction-sections', '-fdata-sections', '-w', '-DNDEBUG',
         '-DLEAN_MULTI_THREAD', '-I' + str(inc), '-I' + str(SRC), '-I' + str(UV / 'include')]
runtime = [(SRC / 'runtime' / f, OUT / 'rt' / (f.replace('/', '_') + '.o'), CXX,
            flags + ['-std=c++20'] + (['-DLEAN_EMSCRIPTEN'] if f == 'openssl.cpp' else []))
           for f in sources('runtime.txt') + ['openssl.cpp']]
uv = [(UV / f, OUT / 'uv' / (f.replace('/', '_') + '.o'), CC,
       ['-O2', '-fPIC', '-w', '-D_GNU_SOURCE', '-D_FILE_OFFSET_BITS=64', '-D_LARGEFILE_SOURCE',
        '-I' + str(UV / 'include'), '-I' + str(UV / 'src')]) for f in sources('uv-linux.txt')]
print(f'Lean {version}, libuv 1.51.0: no mimalloc, no GMP, OpenSSL stubbed', flush=True)
parallel(compile_one, runtime + uv)
archive('libleanrt.a', [o for _, o, _, _ in runtime])
archive('libuv.a', [o for _, o, _, _ in uv])


def core_c(module):
    rel = Path(module.replace('.', '/'))
    source = LEAN / 'src/lean' / rel.with_suffix('.lean')
    dest = OUT / 'c' / rel.with_suffix('.c')
    stamp = dest.with_suffix('.sha')
    digest = hashlib.sha256(source.read_bytes() + version.encode()).hexdigest()
    if not dest.exists() or not stamp.exists() or stamp.read_text() != digest:
        dest.parent.mkdir(parents=True, exist_ok=True)
        temp = dest.with_suffix('.tmp.c')
        run([LEAN / 'bin/lean', '-c', temp, source], dest.with_suffix('.log'), LEAN / 'src/lean')
        temp.replace(dest)
        stamp.write_text(digest)
    return dest


init = ['Init'] + [str(p.relative_to(LEAN / 'src/lean').with_suffix('')).replace('/', '.')
                   for p in sorted((LEAN / 'src/lean/Init').rglob('*.lean'))]
print(f'Generating and compiling {len(init)} Init modules', flush=True)
parallel(core_c, init)
init_objects = [(OUT / 'c' / (m.replace('.', '/') + '.c'), OUT / 'init' / (m + '.o'), CC, flags)
                for m in init]
parallel(compile_one, init_objects)
archive('libInit.a', [o for _, o, _, _ in init_objects])
if '--runtime-only' in sys.argv:
    sys.exit(0)

targets = dict(re.findall(r'lean_exe (\w+) where\s+root := `(tests\.engine\.\w+)',
                          (ROOT / 'lakefile.lean').read_text()))
run([ELAN / 'bin/lake', 'build', *targets], OUT / 'lake.log')
modules = {}


def closure(module):
    if module == 'Init' or module.startswith('Init.'):
        return set()
    if module in modules:
        return modules[module][1]
    rel = Path(module.replace('.', '/'))
    local = ROOT / rel.with_suffix('.lean')
    source = local if local.exists() else LEAN / 'src/lean' / rel.with_suffix('.lean')
    c = ROOT / '.lake/build/ir' / rel.with_suffix('.c') if local.exists() else core_c(module)
    deps = {module}
    for dep in re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', source.read_text(), re.M):
        deps |= closure(dep)
    modules[module] = (c, deps)
    return deps


for main in targets.values():
    closure(main)
print(f'Compiling {len(modules)} engine/test/Std modules with the phone headers', flush=True)
objects = {m: OUT / 'modules' / (m + '.o') for m in modules}
parallel(compile_one, [(c, objects[m], CC, flags) for m, (c, _) in modules.items()])
native = [(ROOT / 'engine/native' / f, OUT / 'native' / (f + '.o'), CC,
           flags + ['-std=gnu11', '-I' + str(ROOT / 'third_party/sqlite')]) for f in ('glue.c', 'crypto.c')]
parallel(compile_one, native)
(OUT / 'bin').mkdir(exist_ok=True)
for exe, main in targets.items():
    run([CXX, '-o', OUT / 'bin' / exe, *[objects[m] for m in sorted(modules[main][1])],
         *[o for _, o, _, _ in native], '-Wl,--start-group', OUT / 'libInit.a', OUT / 'libleanrt.a',
         OUT / 'libuv.a', ROOT / '.lake/build/lib/libsqlite.a',
         ROOT / 'engine/native/crypto/target/release/liblq_crypto.a', '-Wl,--end-group',
         '-pthread', '-ldl', '-lm', '-lrt'], OUT / 'bin' / (exe + '.log'))
print(f'Built {len(targets)} engine suites in {OUT / "bin"}', flush=True)
