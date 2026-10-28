#!/usr/bin/env python3
"""Faults in the actual bounded cache, runtime hook, locale policy and cmap.
Restores source after every fault. Run without another build in progress.
"""
from pathlib import Path
import subprocess
import os
ROOT=Path(__file__).resolve().parents[2]
os.chdir(ROOT)
OUT=ROOT/'out/cjk-negative';OUT.mkdir(parents=True,exist_ok=True)

def run(cmd):
 p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 return p.returncode,p.stdout

def fault(name,path,old,new,proof=False):
 p=ROOT/path;s=p.read_text();assert old in s,name
 try:
  p.write_text(s.replace(old,new,1))
  rc,log=run(['lake','build','engine.renderer.Ttf.Cache' if proof else 'cjk'])
  if proof:
   assert rc and 'error: engine/renderer/Ttf/Cache.lean:' in log,(name,log[-2500:])
  else:
   assert rc==0,(name,'compile failure',log[-2500:])
   rc,output=run(['.lake/build/bin/cjk','out/cjk']);log+=output
   assert rc,(name,'control passed')
  (OUT/f'{name}.log').write_text(log)
  print('rejected:',name,flush=True)
 finally:p.write_text(s)

fault('empty-bound','engine/renderer/Ttf/Cache.lean','Array.replicate capacity none','Array.replicate (capacity + 1) none',True)
fault('checked-bound','engine/renderer/Ttf/Cache.lean','if Valid s then s else empty','s',True)
fault('put-bound','engine/renderer/Ttf/Cache.lean','checked (putRaw s key bitmap)','putRaw s key bitmap',True)
fault('payload-charge','engine/renderer/Ttf/Cache.lean','2 * e.bitmap.pixels.size + 512','0',True)
fault('eviction','engine/renderer/Ttf/Cache.lean','if used ≤ budget then break','if true then break')
fault('runtime-bound','engine/renderer/Ttf/Memo.lean','let cache := Cache.put s.cache key bitmap','let cache := { s.cache with slots := s.cache.slots.push (some ⟨key,bitmap⟩) }')
fault('font-key','engine/renderer/Ttf/Memo.lean','⟨f.uid, glyph, f.size, f.cell⟩','⟨0, glyph, f.size, f.cell⟩')
fault('locale','engine/renderer/Cjk.lean','else [0,1,2,3]','else [2,1,0,3]')
fault('korean-cmap','engine/renderer/Ttf/Cmap.lean','twice > 16378','twice > 8192')
rc,log=run(['bash','tests/app/cjk.sh']);(OUT/'restored.log').write_text(log)
assert rc==0,log[-4000:]
print('9 controls rejected; restored reference/cache/scroll suite passes',flush=True)
