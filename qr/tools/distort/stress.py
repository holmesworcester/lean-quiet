#!/usr/bin/env python3
"""Where the decoder stops: one distortion at a time pushed past the camera
suite's range, for the README's limits (not a gate).

usage: stress.py QR_TOOL WORKDIR LABEL=symbol.pgm...
Prints, per distortion and level, how many of the symbols decoded.
"""
import os
import subprocess
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
from cases import fit, side_of  # noqa: E402
tool, work = sys.argv[1], sys.argv[2]
syms = [a.split('=', 1) for a in sys.argv[3:]]
os.makedirs(work, exist_ok=True)
sweeps = [
    ('mod', [2.0, 2.5, 3.0], dict(rot=5, blur=0.4, noise=3)),
    ('blur', [1.6, 2.0, 2.5, 3.0], dict(mod=5, rot=20, noise=2)),
    ('noise', [28, 40, 55, 70], dict(rot=-8, blur=0.6)),
    ('tilt', [0.3, 0.4, 0.5], dict(rot=10, skew=45, blur=0.5, noise=3)),
    ('contrast', [0.25, 0.15, 0.1], dict(rot=40, blur=0.5, noise=3)),
    ('light', [0.85, 0.92, 0.97], dict(rot=12, blur=0.5, noise=4)),
    ('occlude', [0.15, 0.2, 0.3, 0.4, 0.45, 0.5], dict(rot=25, blur=0.5, noise=3)),
]
for key, levels, base in sweeps:
    for lv in levels:
        rows = []
        for label, path in syms:
            o = dict(base, **{key: lv})
            o['mod'] = fit(side_of(path), float(o.get('mod', 5)), float(o.get('rot', 0)))
            rows.append(f'{key}{lv}-{label}\t{path}\t' + ' '.join(f'{k}={v}' for k, v in o.items()))
        tsv = f'{work}/cases.tsv'
        open(tsv, 'w').write('\n'.join(rows) + '\n')
        subprocess.run([sys.executable, f'{here}/distort.py', tsv, work], check=True, capture_output=True)
        frames = [f'{work}/{r.split(chr(9))[0]}.pgm' for r in rows]
        out = subprocess.run([tool, 'decode', *frames], capture_output=True, check=True).stdout.decode()
        ok = [line.split()[0].rsplit('-', 1)[1][:-4] for line in out.splitlines() if line.split()[1] == 'ok']
        print(f'{key}={lv}: decoded {len(ok)}/{len(rows)} ({" ".join(sorted(ok))})')
