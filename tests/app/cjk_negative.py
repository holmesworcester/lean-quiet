#!/usr/bin/env python3
"""Faults in the running glyph memo, locale policy and cmap.
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
  rc,log=run(['lake','build','engine.renderer.Ttf.Memo' if proof else 'cjk'])
  if proof:
   assert rc and 'error: engine/renderer/Ttf/Memo.lean:' in log,(name,log[-2500:])
  else:
   assert rc==0,(name,'compile failure',log[-2500:])
   rc,output=run(['.lake/build/bin/cjk','out/cjk']);log+=output
   assert rc,(name,'control passed')
  (OUT/f'{name}.log').write_text(log)
  print('rejected:',name,flush=True)
 finally:p.write_text(s)

# A size keeping another size's table: its type names the size, so it cannot.
fault('size-alias','engine/renderer/Ttf/Memo.lean','  make f.font size cell\n\n/-- The same face','  { f with size, cell }\n\n/-- The same face',True)
# The memo not run: every read rasters afresh, so no read is the kept glyph.
fault('memo-off','engine/renderer/Ttf/Memo.lean','@[csimp] theorem bitmap_eq_fast','theorem bitmap_eq_fast')
fault('locale','engine/renderer/Cjk.lean','else [0,1,2,3]','else [2,1,0,3]')
fault('korean-cmap','engine/renderer/Ttf/Cmap.lean','twice > 16378','twice > 8192')
rc,log=run(['bash','tests/app/cjk.sh']);(OUT/'restored.log').write_text(log)
assert rc==0,log[-4000:]
print('4 controls rejected; restored reference/memo/scroll suite passes',flush=True)
