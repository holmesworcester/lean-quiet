"""Ensure reviewed phone ceilings reject missing rows and the old fake glyphs."""
import json
import shutil
from pathlib import Path
from PIL import Image, ImageDraw
from compare import compare

root = Path(__file__).resolve().parents[2]
reference = root / 'tests/visual/mobile-switcher-reference'
actual = root / 'out/visual/mobile-switcher-actual'
budgets = json.loads((root / 'tests/visual/mobile-switcher-budgets.json').read_text())
for mutation in ['missing-community', 'missing-actions', 'shifted-sheet']:
    target = root / 'out/visual/mobile-switcher-negative' / mutation
    target.mkdir(parents=True, exist_ok=True)
    for original in actual.glob('*.ppm'):
        im = Image.open(original).convert('RGB')
        w = min(320, im.width - 56)
        panel = im.getpixel((80, 400))
        draw = ImageDraw.Draw(im)
        if mutation == 'missing-community':
            draw.rectangle((8, 68, w - 9, 125), fill=panel)
        elif mutation == 'missing-actions':
            for y in [153, 211, 269]:
                draw.rectangle((19, y, 55, y + 36), fill=panel)
        else:
            im.paste(im.crop((0, 0, w, im.height)), (8, 0))
        im.save(target / original.name)
        shutil.copyfile(original.with_suffix('.popup.tsv'), target / original.with_suffix('.popup.tsv').name)
    _, failures = compare(reference, target, target / 'report', budgets)
    rejected = {f.split(':')[0] for f in failures}
    assert set(budgets) <= rejected, (mutation, 'mutation escaped', set(budgets) - rejected)
print('mobile switcher: missing communities, missing action glyphs and shifted sheet rejected in all six reference cases')
