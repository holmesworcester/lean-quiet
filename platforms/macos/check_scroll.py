#!/usr/bin/env python3
"""Compare actual AppKit snapshots taken while its native viewport moves.
The source publication is deliberately stale; only the message pixels may
translate. Fixed chrome must remain byte-identical, including the composer.
"""
import json
from pathlib import Path
import sys
from PIL import Image, ImageChops

out=Path(sys.argv[1])
b=json.loads((out/'native-in-flight.json').read_text())
before=Image.open(out/'native-in-flight-source.png').convert('RGB')
during=Image.open(out/'native-in-flight.png').convert('RGB')
initial=Image.open(out/'native-before.png').convert('RGB')
assert before.size==during.size
x,y,w,h=b['viewport']
delta=b['sample']-b['base']
assert b['sample']!=b['base'] and 0<delta<h-32, 'snapshot did not catch an untranslated Lean publication'
regions={'sidebar':(0,0,x,before.height),
         'header':(0,0,before.width,y),
         'composer-toolbar':(0,y+h,before.width,before.height)}
for name,rect in regions.items():
    assert ImageChops.difference(before.crop(rect),during.crop(rect)).getbbox() is None, f'{name} differs from its fixed publication'
    assert ImageChops.difference(initial.crop(rect),during.crop(rect)).getbbox() is None, f'{name} moved during native scrolling'
assert ImageChops.difference(before.crop((x,y,x+w,y+h)),during.crop((x,y,x+w,y+h))).getbbox(), 'message viewport did not move'
# Exclude the native overlay scroller. Check ink, not empty background,
# against its expected translation from the exact same cached publication.
old=before.crop((x+8,y+8,x+w-40,y+h-delta-8))
new=during.crop((x+8,y+8+delta,x+w-40,y+h-8))
ground=before.getpixel((x+4,y+4))
ink=matches=0
old_pixels=old.get_flattened_data() if hasattr(old,"get_flattened_data") else old.getdata()
new_pixels=new.get_flattened_data() if hasattr(new,"get_flattened_data") else new.getdata()
for p,q in zip(old_pixels,new_pixels):
    if sum(abs(p[i]-ground[i]) for i in range(3))>24:
        ink+=1; matches+=p==q
ratio=matches/max(1,ink)
assert ink>500 and ratio>.995, f'native crop/translation corrupts ink: {matches}/{ink}'
comparison=json.loads((out/'scroll-comparison.json').read_text())
assert comparison['native']['updates_without_Lean_frame']>=3
assert comparison['legacy']['updates_without_Lean_frame']==0
report={'delta_pixels':delta,'ink_pixels':ink,'translated_ink_match':ratio,
        'fixed_regions':list(regions),'native_updates_without_Lean_frame':comparison['native']['updates_without_Lean_frame'],
        'legacy_updates_without_Lean_frame':0}
(out/'scroll-pixels.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'Native scroll pixels: {ratio:.3%} ink preserved; sidebar, header, composer and toolbar fixed')
