"""Deliberately break actual rendered hover frames; the same gate must fail."""
import json
from pathlib import Path
import shutil
import numpy as np
from PIL import Image
from compare_hover import compare

ROOT=Path(__file__).resolve().parents[2]
budgets=json.loads((ROOT/'tests/visual/hover-budgets.json').read_text())
count=0
for theme in ['light','dark']:
    for control in ['team','settings-row','composer','message']:
        name=f'hover-{control}-{theme}'
        for mutation in ['missing','wrong-color','shifted']:
            folder=ROOT/'out/visual/hover-negative'/f'{name}-{mutation}'
            ref,actual=folder/'reference',folder/'actual'
            for p in [ref/'rest',actual/'rest']: p.mkdir(parents=True,exist_ok=True)
            for ext in ['png','hover.json']:
                shutil.copyfile(ROOT/f'tests/visual/hover-reference/{name}.{ext}',ref/f'{name}.{ext}')
            shutil.copyfile(ROOT/f'tests/visual/hover-reference/rest/{name}.png',ref/'rest'/f'{name}.png')
            original=ROOT/f'out/visual/hover-actual/{name}.ppm'
            rest=ROOT/f'out/visual/hover-actual/rest/{name}.ppm'
            shutil.copyfile(rest,actual/'rest'/f'{name}.ppm')
            before=np.array(Image.open(rest).convert('RGB'),dtype=np.int16)
            observed=np.array(Image.open(original).convert('RGB'),dtype=np.int16)
            delta=observed-before
            if mutation=='missing': observed=before
            elif mutation=='wrong-color': observed[np.abs(delta).max(2)>0]=[0,255,0]
            else: observed=np.clip(before+np.roll(delta,8,axis=1),0,255)
            Image.fromarray(observed.astype(np.uint8)).save(actual/f'{name}.ppm')
            _,failures=compare(ref,actual,folder/'report',{name:budgets[name]})
            assert failures,f'{name}/{mutation} escaped the gate'
            count+=1
print(f'hover pixel gate: rejected all {count} real-frame regressions')
