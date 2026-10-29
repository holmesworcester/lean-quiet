"""Exercise the reviewed gate with visible regressions in real rendered frames.

References stay read-only. Bad frames and their reports remain under out/visual
so the exact missing content, displacement and edge regressions are reviewable.
"""
import json
from pathlib import Path
import shutil

from PIL import Image, ImageDraw
from compare import compare

ROOT = Path(__file__).resolve().parents[2]


def main():
    budgets = json.loads((ROOT / 'tests/visual/switcher-budgets.json').read_text())
    out = ROOT / 'out/visual/switcher-negative'
    count = 0
    for theme in ['light', 'dark']:
        name = f'switcher-1280-{theme}'
        for mutation in ['missing-content', 'moved-popup', 'heavy-border', 'wrong-geometry']:
            folder = out / f'{theme}-{mutation}'
            ref, actual = folder / 'reference', folder / 'actual'
            ref.mkdir(parents=True, exist_ok=True)
            actual.mkdir(parents=True, exist_ok=True)
            for ext in ['png', 'json']:
                shutil.copyfile(ROOT / f'tests/visual/switcher-reference/{name}.{ext}', ref / f'{name}.{ext}')
            shutil.copyfile(ROOT / f'out/visual/switcher-actual/{name}.popup.tsv', actual / f'{name}.popup.tsv')
            image = Image.open(ROOT / f'out/visual/switcher-actual/{name}.ppm').convert('RGB')
            draw = ImageDraw.Draw(image)
            if mutation == 'missing-content':
                draw.rectangle((17, 105, 298, 350), fill='#ffffff' if theme == 'light' else '#222222')
            elif mutation == 'moved-popup':
                image.paste(image.crop((8, 48, 308, 363)), (12, 48))
            elif mutation == 'heavy-border':
                draw.rectangle((8, 48, 307, 362), outline='#222222' if theme == 'light' else '#eaeaea', width=3)
            else:
                geometry = actual / f'{name}.popup.tsv'
                values = geometry.read_text().split()
                values[0] = str(int(values[0]) + 8)
                geometry.write_text('\t'.join(values) + '\n')
            image.save(actual / f'{name}.ppm')
            _, failures = compare(ref, actual, folder / 'report', {name: budgets[name]})
            expected = 'geometry' if mutation == 'wrong-geometry' else 'popup_'
            if not any(expected in failure for failure in failures):
                raise AssertionError(f'{theme}/{mutation} escaped the independent popup gate: {failures}')
            count += 1
    print(f'switcher pixel gate: rejected all {count} real-frame regressions')


if __name__ == '__main__':
    main()
