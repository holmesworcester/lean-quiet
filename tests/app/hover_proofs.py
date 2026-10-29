"""Reject broken runtime hover rules with the real Lean proofs, in isolated copies.

No edit to a running checkout and no source mirror: each case mutates exactly
the source the renderer imports and compiles the unchanged production laws.
"""
import os
from pathlib import Path
import subprocess as sp

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'out/hover-proof-negative'
source=(ROOT/'engine/renderer/Hover.lean').read_text()
mutations=[
 ('disabled','enabled && p.any b.has','p.any b.has'),
 ('right-edge','p.1 < b.x + b.w','p.1 ≤ b.x + b.w'),
 ('z-order','surfaces.find?','surfaces.reverse.find?'),
 ('leave','| .leave | .blur | .touch => none','| .leave => some (0, 0)\n  | .blur | .touch => none'),
]
for name,old,new in mutations:
    assert old in source,name
    folder=OUT/name
    module=folder/'engine/renderer/Hover.lean'
    module.parent.mkdir(parents=True,exist_ok=True)
    module.write_text(source.replace(old,new))
    env=dict(os.environ,LEAN_PATH=str(folder)+':'+str(ROOT/'.lake/build/lib/lean'))
    def run(args):
        return sp.run(['lean',*map(str,args)],cwd=ROOT,env=env,stdout=sp.PIPE,stderr=sp.STDOUT,text=True,timeout=60)
    built=run(['-o',module.with_suffix('.olean'),module])
    (folder/'build.log').write_text(built.stdout)
    assert built.returncode==0,built.stdout
    proof=run([ROOT/'engine/renderer/HoverLaws.lean'])
    (folder/'proof.log').write_text(proof.stdout)
    assert proof.returncode!=0 and 'error:' in proof.stdout and 'sorry' not in proof.stdout, (name,proof.stdout)
    print('proof rejected',name,flush=True)
print('hover proof negative controls: all 4 incorrect runtime rules rejected')
