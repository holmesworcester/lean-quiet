"""Prove the composer gate catches the reported divider/spacing regressions."""
import json
from pathlib import Path
import shutil

from PIL import Image, ImageDraw
from compare import compare

ROOT = Path(__file__).resolve().parents[2]


def main():
    budgets = json.loads((ROOT / 'tests/visual/composer-budgets.json').read_text())
    count = 0
    for theme in ['light', 'dark']:
        for width in [390, 1280]:
            name = f'composer-empty-{width}-100-{theme}'
            oracle = json.loads((ROOT / f'tests/visual/composer-reference/{name}.composer.json').read_text())
            for mutation in ['divider', 'toolbar-shift', 'text-baseline', 'field-height']:
                folder = ROOT / f'out/visual/composer-negative/{name}/{mutation}'
                ref, actual = folder / 'reference', folder / 'actual'
                ref.mkdir(parents=True, exist_ok=True)
                actual.mkdir(parents=True, exist_ok=True)
                for ext in ['png', 'composer.json']:
                    shutil.copyfile(ROOT / f'tests/visual/composer-reference/{name}.{ext}', ref / f'{name}.{ext}')
                geometry = actual / f'{name}.composer.tsv'
                shutil.copyfile(ROOT / f'out/visual/composer-actual/{name}.composer.tsv', geometry)
                frame = Image.open(ROOT / f'out/visual/composer-actual/{name}.ppm').convert('RGB')
                panel = '#ffffff' if theme == 'light' else '#222222'
                draw = ImageDraw.Draw(frame)
                x,y,w,h = map(round,oracle['field'])
                if mutation == 'divider':
                    # Erase the mobile rule; introduce one inside desktop.
                    draw.line((x+20,y+h,x+w-21,y+h), fill=panel if width == 390 else '#808080')
                elif mutation == 'toolbar-shift':
                    top = round(oracle['buttons'][0]['box'][1])
                    strip = frame.crop((x,top,x+w,top+44))
                    draw.rectangle((x,top-4,x+w-1,top+43),fill=panel)
                    frame.paste(strip,(x,top-4))
                elif mutation == 'text-baseline':
                    strip = frame.crop((x+16,y+10,x+w-16,y+h-5))
                    draw.rectangle((x+16,y+6,x+w-17,y+h-6),fill=panel)
                    frame.paste(strip,(x+16,y+6))
                else:
                    boxes = [line.split() for line in geometry.read_text().splitlines()]
                    boxes[2][3] = str(int(boxes[2][3])+4)
                    geometry.write_text(''.join('\t'.join(box)+'\n' for box in boxes))
                frame.save(actual / f'{name}.ppm')
                _, failures = compare(ref,actual,folder/'report',{name:budgets[name]})
                expected = 'geometry' if mutation == 'field-height' else 'gap or divider' if mutation == 'divider' else 'composer_'
                if not any(expected in f for f in failures):
                    raise AssertionError(f'accepted {name}/{mutation}: {failures}')
                count += 1
    print(f'composer: rejected {count} divider, toolbar, text-baseline and field-height regressions')


if __name__ == '__main__':
    main()
