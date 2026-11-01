#!/usr/bin/env python3
"""Compile bad cache cores, reject pixels/proofs, and test the actual App caller."""
from pathlib import Path
import subprocess
import sys

root, logs = map(Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)
cap = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']

def run(args, name):
    try:
        p = subprocess.run(args, cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, timeout=240)
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b''
        if isinstance(out, bytes): out = out.decode(errors='replace')
        (logs/(name+'.log')).write_text(out+'\nTIMEOUT\n')
        raise
    (logs/(name+'.log')).write_text(p.stdout)
    return p

def build(targets, name):
    p = run(cap+['lake', 'build']+targets, name)
    assert p.returncode == 0, (name, 'must compile', p.stdout[-2000:])

def runtime(name, good):
    p = run([str(root/'.lake/build/bin/hold_cache')], name)
    assert not any(x in p.stdout.lower() for x in ['panic', 'uncaught exception', 'segmentation fault', 'assertion violation'])
    assert p.returncode == (0 if good else 1), (name, p.stdout)
    assert ('36 actual pixel/key checks passed' if good else 'FAIL: cached plane differs from existing pixel generator') in p.stdout

source=root/'engine/renderer/HoldCache.lean'
original=source.read_text()
key='⟨s.bgRow, s.W, s.dim.dpi, s.dim.theme⟩'
cases=[('omit-background', key, '⟨.empty, s.W, s.dim.dpi, s.dim.theme⟩'),
       ('omit-width', key, '⟨s.bgRow, 0, s.dim.dpi, s.dim.theme⟩'),
       ('omit-density', key, '⟨s.bgRow, s.W, 0, s.dim.theme⟩'),
       ('omit-theme', key, '⟨s.bgRow, s.W, s.dim.dpi, .dark⟩'),
       ('wrong-key-reuse', 'if old.key = key then old', 'if True then old')]
build(['engine.renderer.HoldCacheLaws','hold_cache','skeleton'], 'baseline-build')
runtime('baseline', True)
p=run([str(root/'.lake/build/bin/skeleton'),str(logs/'baseline-skeleton')], 'baseline-skeleton')
assert p.returncode==0 and 'skeleton: 32 ' in p.stdout,p.stdout
try:
    for name, old, new in cases:
        assert original.count(old)==1,(name,'anchor')
        source.write_text(original.replace(old,new))
        build(['hold_cache'], name+'-build')
        runtime(name+'-runtime', False)
        p=run(cap+['lake','env','lean','engine/renderer/HoldCacheLaws.lean'], name+'-laws')
        assert p.returncode==1 and 'error:' in p.stdout and 'sorry' not in p.stdout.lower(),(name,p.stdout)
        assert 'unknown module' not in p.stdout.lower() and 'object file' not in p.stdout.lower(),(name,p.stdout)
        print('rejected:',name,flush=True)
finally:
    source.write_text(original)
build(['engine.renderer.HoldCacheLaws','hold_cache','skeleton'],'restored-core-build')
runtime('restored-core',True)
app=root/'app/Screen.lean'
saved=app.read_text()
needle='Hold.cachedMessagePlane s.holdCache'
assert saved.count(needle)==1
try:
    app.write_text(saved.replace(needle,'Hold.cachedMessagePlane none'))
    build(['skeleton'],'always-empty-build')
    p=run([str(root/'.lake/build/bin/skeleton'),str(logs/'always-empty-skeleton')],'always-empty-skeleton')
    assert p.returncode==1 and 'FAIL skeleton: actual App.present reuses cached skeleton pixel objects' in p.stdout,p.stdout
    assert not any(x in p.stdout.lower() for x in ['panic','uncaught exception','segmentation fault','assertion violation'])
    print('rejected: actual App caller discards the cache',flush=True)
finally:
    app.write_text(saved)
build(['skeleton'],'restored-app-build')
p=run([str(root/'.lake/build/bin/skeleton'),str(logs/'restored-skeleton')],'restored-skeleton')
assert p.returncode==0 and 'skeleton: 32 ' in p.stdout,p.stdout
print('hold cache: 36 pixel/key checks,32 actual App skeleton cases,6 compiling controls,restored pass',flush=True)
