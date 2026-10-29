"""Independent DOM-targeted hover oracle, including paired resting pixels.

The delta gate isolates hover from pre-existing font/layout differences. A
missing hover cannot pass by occupying a tiny fraction of the full window.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from PIL import Image
from compare import metrics

ROOT = Path(__file__).resolve().parents[2]

def compare(reference, actual, out, budgets=None):
    out.mkdir(parents=True, exist_ok=True)
    results, failures, cards = {}, [], []
    for specfile in sorted(reference.glob('*.hover.json')):
        name = specfile.name.removesuffix('.hover.json')
        spec = json.loads(specfile.read_text())
        region = tuple(spec['region'])
        frames = [Image.open(p).convert('RGB') for p in [reference/f'{name}.png',reference/'rest'/f'{name}.png',actual/f'{name}.ppm',actual/'rest'/f'{name}.ppm']]
        expected, rest, observed, before = [im.crop(region) for im in frames]
        arrays = [np.asarray(im,dtype=np.float32) for im in [expected,rest,observed,before]]
        delta, native = arrays[0]-arrays[1], arrays[2]-arrays[3]
        expected_active = np.abs(delta).max(2)>0.5
        native_active = np.abs(native).max(2)>0.5
        score,_ = metrics(expected,observed,sidebar=False)
        score['delta_mae'] = float(np.abs(delta-native).mean()/255)
        score['recall'] = float((expected_active & native_active).sum()/max(1,expected_active.sum()))
        score['precision'] = float((expected_active & native_active).sum()/max(1,native_active.sum()))
        # Cursor-only or disabled targets must remain exactly at rest in Lean.
        if not expected_active.any():
            if native_active.any(): failures.append(f'{name}: cursor-only/disabled target acquired a visual hover')
        elif not native_active.any():
            failures.append(f'{name}: visible reference hover is missing')
        results[name] = score
        if budgets is not None:
            if name not in budgets: failures.append(f'{name}: unreviewed case')
            else:
                for key,limit in budgets[name].items():
                    bad = score[key]<limit if key in ['recall','precision'] else score[key]>limit
                    if bad: failures.append(f'{name}: {key} {score[key]:.5f} outside {limit:.5f}')
        for label,im in [('reference',expected),('actual',observed),('rest',before)]: im.save(out/f'{name}-{label}.png')
        heat=np.minimum(255,np.abs(delta-native)*8).astype(np.uint8)
        Image.fromarray(heat).save(out/f'{name}-delta-diff.png')
        cards.append(f'<article><h2>{name}</h2><pre>{json.dumps(score)}</pre>'+''.join(f'<figure><figcaption>{label}</figcaption><img src="{name}-{label}.png"></figure>' for label in ['reference','actual','rest','delta-diff'])+'</article>')
    if budgets is not None:
        failures += [f'{name}: missing case' for name in budgets.keys()-results.keys()]
    (out/'metrics.json').write_text(json.dumps(results,indent=2)+'\n')
    (out/'index.html').write_text('<!doctype html><meta charset="utf-8"><title>Hover pixel oracle</title><style>body{font:14px sans-serif}article{border-bottom:1px solid #888}figure{display:inline-block;vertical-align:top;margin:8px}img{max-width:100%}</style>'+''.join(cards))
    return results,failures

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--budgets',type=Path)
    args=p.parse_args()
    result,fail=compare(ROOT/'tests/visual/hover-reference',ROOT/'out/visual/hover-actual',ROOT/'out/visual/hover-report',json.loads(args.budgets.read_text()) if args.budgets else None)
    print(f'hover oracle: {len(result)} DOM targets; {len(fail)} failures')
    if fail: raise SystemExit('\n'.join(fail))
