"""Independent DOM geometry versus the actual Lean screenshot's track geometry."""
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
checks=0
for line in (ROOT/'tests/zoom/cases.tsv').read_text().splitlines():
    if not line or line.startswith('#'): continue
    name,w,h,theme,page,percent=line.split('\t')
    z=int(percent)/100
    dom=json.loads((ROOT/f'tests/zoom/reference/{name}.json').read_text())
    raw=(ROOT/f'out/zoom/actual/{name}.geometry.txt').read_text()
    tracks={key:tuple(map(int,re.search(key+r'=(\d+),(\d+)',raw).groups())) for key in ['nav','main','context']}
    # The reference's narrow pane-list is the full home page, not a
    # sidebar. Only a visible thread to its right establishes navigation.
    main=next((r for r in dom if r['selector'].startswith('pane pane-thread') and r['w']>0),None)
    expected_nav=main['x']*z if main else 0
    assert abs(tracks['nav'][1]-expected_nav)<=2,(name,tracks,expected_nav)
    if main:
        assert abs(tracks['main'][0]-main['x']*z)<=2,(name,tracks,main)
        assert abs(tracks['main'][1]-main['w']*z)<=2,(name,tracks,main)
    drawer=next((r for r in dom if r['selector'].startswith('drawer ') and r['w']>0),None)
    if drawer:
        actual=tracks['context'] if tracks['context'][1] else tracks['main']
        assert abs(actual[0]-drawer['x']*z)<=2,(name,actual,drawer)
        assert abs(actual[1]-drawer['w']*z)<=2,(name,actual,drawer)
    checks+=1
print(f'zoom parity: {checks} independent libquiet DOM layouts match native tracks within 2 device pixels')
