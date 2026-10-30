#!/usr/bin/env python3
"""Reject blank backing layers during real OS edge drags and after release.
Read the compositor capture made BEFORE the repainting NSView snapshot.
"""
import json
from pathlib import Path
import sys
from PIL import Image

out=Path(sys.argv[1])
report={}
for direction in ['grow','shrink']:
    for phase in ['live','settled']:
        name=f'resize-{direction}-{phase}'
        meta=json.loads((out/(name+'.json')).read_text())
        actual=Image.open(out/(name+'-backing.png')).convert('RGB')
        source=Image.open(out/(name+'-source.png')).convert('RGB')
        assert actual.size==source.size, f'{name}: backing size differs'
        # Normalize the published layout to the current window, just as the
        # fallback desktop image is scaled during the drag.
        pw,ph=meta['publicationSize']
        x,y,w,h=meta['viewport']
        x=round(x*actual.width/pw); y=round(y*actual.height/ph)
        bottom=round((meta['viewport'][1]+h)*actual.height/ph)
        regions={'sidebar':(0,0,x,actual.height),
                 'conversation':(x,y,actual.width-32,bottom),
                 'composer-toolbar':(x,bottom,actual.width,actual.height)}
        counts={}
        for label,box in regions.items():
            def ink(im):
                pixels=im.crop(box)
                values=pixels.get_flattened_data() if hasattr(pixels,'get_flattened_data') else pixels.getdata()
                return sum(min(p)<220 for p in values)
            expected=ink(source); seen=ink(actual)
            assert expected>100, f'{name} {label}: empty reference fixture'
            assert seen>=expected*.85, f'{name} {label}: blank backing ({seen}/{expected} ink pixels)'
            counts[label]={'expected_ink':expected,'displayed_ink':seen}
        report[name]=counts
(out/'resize-pixels.json').write_text(json.dumps(report,indent=2)+'\n')
print('Resize pixels: sidebar, conversation and composer remain visible during grow/shrink drags and after release')
