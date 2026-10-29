"""Fingerprint APK inputs, including ignored assets and the Android runtime.
The test can reuse an identical build while always executing its native suite.
"""
import hashlib
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[2]
rt=Path(os.environ.get('LEANRT',str(ROOT/'out/leanrt')))
sdk=Path(os.environ.get('ANDROID_SDK',str(Path.home()/'android-sdk')))
files=[]
for name in subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines():
    if ((name.endswith('.lean') and (name.startswith(('engine/','ops/')) or '/' not in name)) or
        name.startswith(('platforms/android/twin/','engine/native/','third_party/','ui/','tools/')) or
        name in ['lean-toolchain','lake-manifest.json']):
        files.append(ROOT/name)
files.extend(p for p in (ROOT/'assets').rglob('*') if p.is_file())
files.extend(rt/abi/'libInit.a' for abi in ['x86_64','arm64-v8a'])
files.extend(p for p in (rt/'include').rglob('*') if p.is_file())
h=hashlib.sha256()
for directory in ['ndk','build-tools','platforms']:
    h.update(str(sorted(p.name for p in (sdk/directory).iterdir())).encode())
for p in sorted(set(files)):
    h.update(str(p).encode()+b'\0')
    with p.open('rb') as f:
        while block:=f.read(1024*1024): h.update(block)
print(h.hexdigest())
