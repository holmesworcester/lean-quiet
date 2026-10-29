"""Compare real rendered frames at identical dimensions; keep reviewable artifacts."""
import argparse
import html
import json
from pathlib import Path
import numpy as np
from PIL import Image, ImageFilter


def metrics(expected, actual):
    if expected.size != actual.size:
        raise ValueError(f'dimensions differ: reference {expected.size}, actual {actual.size}')
    a = np.asarray(expected.convert('RGB'), dtype=np.float32)
    b = np.asarray(actual.convert('RGB'), dtype=np.float32)
    diff = np.abs(a - b)
    # Small spatial pooling reports broad layout independently of glyph AA.
    size = (max(1, expected.width // 8), max(1, expected.height // 8))
    coarse_a = np.asarray(expected.resize(size, Image.Resampling.BOX), dtype=np.float32)
    coarse_b = np.asarray(actual.resize(size, Image.Resampling.BOX), dtype=np.float32)
    return {
        'mae': float(diff.mean() / 255),
        'changed_fraction': float((diff.max(axis=2) > 16).mean()),
        'layout_mae': float(np.abs(coarse_a - coarse_b).mean() / 255),
    }, diff


def compare(reference, actual, out, budgets=None):
    out.mkdir(parents=True, exist_ok=True)
    results, failures, cards = {}, [], []
    cases = sorted(reference.glob('*.png'))
    if not cases:
        raise ValueError(f'no reference cases in {reference}')
    for expected_file in cases:
        name = expected_file.stem
        actual_file = actual / f'{name}.ppm'
        if not actual_file.exists():
            failures.append(f'{name}: missing actual frame')
            continue
        expected = Image.open(expected_file).convert('RGB')
        observed = Image.open(actual_file).convert('RGB')
        scores, diff = metrics(expected, observed)
        results[name] = scores
        expected.save(out / f'{name}-reference.png')
        observed.save(out / f'{name}-actual.png')
        heat = np.zeros_like(diff, dtype=np.uint8)
        heat[:, :, 0] = np.minimum(255, diff.max(axis=2) * 4).astype(np.uint8)
        Image.fromarray(heat).save(out / f'{name}-diff.png')
        Image.blend(expected, observed, .5).save(out / f'{name}-overlay.png')
        if budgets is not None:
            if name not in budgets:
                failures.append(f'{name}: no reviewed budget')
            else:
                for metric, limit in budgets[name].items():
                    if scores[metric] > limit:
                        failures.append(f'{name}: {metric} {scores[metric]:.5f} > {limit:.5f}')
        cards.append(f'<article><h2>{html.escape(name)}</h2><p>{html.escape(json.dumps(scores))}</p>'
                     + ''.join(f'<figure><figcaption>{kind}</figcaption><img src="{name}-{kind}.png"></figure>'
                               for kind in ['reference', 'actual', 'diff', 'overlay']) + '</article>')
    if budgets is not None:
        for name in budgets.keys() - results.keys():
            failures.append(f'{name}: reviewed case was not rendered')
    (out / 'metrics.json').write_text(json.dumps(results, indent=2) + '\n')
    (out / 'index.html').write_text('<!doctype html><meta charset="utf-8"><title>Quiet pixel comparison</title>'
        '<style>body{font:14px system-ui;margin:24px}article{border-bottom:1px solid #ccc;padding:16px 0}'
        'figure{display:inline-block;vertical-align:top;margin:8px}img{max-width:420px;border:1px solid #ccc}'
        'figcaption{font-weight:600;margin-bottom:8px}</style><h1>Quiet / libquiet pixel comparison</h1>'
        + ''.join(cards))
    return results, failures


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('reference', type=Path)
    p.add_argument('actual', type=Path)
    p.add_argument('out', type=Path)
    p.add_argument('--budgets', type=Path)
    a = p.parse_args()
    budgets = json.loads(a.budgets.read_text()) if a.budgets else None
    results, failures = compare(a.reference, a.actual, a.out, budgets)
    print(json.dumps(results, indent=2))
    for failure in failures:
        print('FAIL:', failure)
    raise SystemExit(bool(failures))

if __name__ == '__main__':
    main()
