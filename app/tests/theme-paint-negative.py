#!/usr/bin/env python3
"""Break the rendering and storage paths; require proof or actual app failure."""
from pathlib import Path
import subprocess
out=Path('out/appearance/negative');out.mkdir(parents=True,exist_ok=True)
cases=[
 ('text-path','Quiet/Paint.lean','Contrast.ink wanted (getPx row x)','wanted','proof'),
 ('scrim-paint','Quiet/Scrim.lean','for s in b.strokes do','for s in (#[] : Array Stroke) do','live'),
 ('edge-paint','Quiet/Overlay.lean','let c := if inside then getPx src i else edge theme (getPx dst (x+i))','let c := if inside then getPx src i else getPx src i','live'),
 ('persistence','Quiet/ThemeStore.lean','INSERT OR REPLACE INTO appearance (id, value) VALUES (1, ?)','SELECT value FROM appearance WHERE value = ?','write'),
]
for name,file,old,new,mode in cases:
 p=Path(file);original=p.read_text();assert old in original
 try:
  p.write_text(original.replace(old,new,1))
  got=subprocess.run(['lake','build','appearance'],capture_output=True,text=True,timeout=150)
  log=got.stdout+got.stderr
  if mode=='proof':
   assert got.returncode != 0 and 'Scrim.lean:' in log, f'{name}: proof did not reject'
  else:
   assert got.returncode == 0, f'{name}: build failed before testing'
   run=subprocess.run(['.lake/build/bin/appearance',mode,str(out/name),'dark'],capture_output=True,text=True,timeout=120)
   log+='\n'+run.stdout+run.stderr
   assert run.returncode != 0 and 'FAIL' in log, f'{name}: broken code passed'
  (out/(name+'.log')).write_text(log)
  print(f'negative {name}: rejected by {mode}',flush=True)
 finally:p.write_text(original)
subprocess.run(['lake','build','appearance','quiet_host'],check=True,stdout=(out/'paint-restored.log').open('w'))
print('4 rendering/storage controls rejected; sources and binaries restored',flush=True)
