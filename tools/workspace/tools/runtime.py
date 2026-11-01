#!/usr/bin/env python3
"""Fetch and verify the optional public browser prover, outside the checkout."""
from pathlib import Path
import hashlib,json,os,subprocess,concurrent.futures
manifest=json.loads(Path(__file__).with_name('runtime.json').read_text())
dest=Path(os.environ.get('QUIET_LEAN_RUNTIME','/mnt/storage/holmes-tmp/quiet-lean-browser-runtime'))
dest.mkdir(parents=True,exist_ok=True)
def digest(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def fetch(item):
    name,expected=item;p=dest/name
    if p.exists() and digest(p)==expected:return f'Verified {name}'
    partial=p.with_suffix(p.suffix+'.partial')
    subprocess.run(['curl','--fail','--location','--silent','--show-error','--retry','2',manifest['baseUrl']+name,'-o',str(partial)],check=True)
    if digest(partial)!=expected:raise RuntimeError('Checksum mismatch: '+name)
    partial.replace(p)
    return f'Downloaded and verified {name}'
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
    for result in pool.map(fetch,manifest['assets'].items()):print(result,flush=True)
