"""Get started's reviewed ceilings must reject what this screen used to get
wrong: a sidebar beside it with no community, the wordmark drawn as a
letter on a disc instead of libquiet's lockup, and a column in the wrong
place (top-anchored on the desktop, or shifted)."""
import json
import shutil
from pathlib import Path
from PIL import Image, ImageDraw
from compare import compare

root = Path(__file__).resolve().parents[2]
reference = root / 'tests/visual/start-reference'
actual = root / 'out/visual/start-actual'
budgets = json.loads((root / 'tests/visual/start-budgets.json').read_text())


def lockup_box(im):
    """The lockup's ink box: the first run of rows holding coloured (not
    grey) pixels from the top, which is the lockup; the caption's emoji is
    far below it."""
    rows = []
    for y in range(im.height):
        xs = [x for x in range(im.width) if (lambda p: max(p) - min(p) > 25)(im.getpixel((x, y)))]
        if xs:
            rows.append((y, min(xs), max(xs)))
        elif rows:
            break
    return min(r[1] for r in rows), rows[0][0], max(r[2] for r in rows), rows[-1][0]


for mutation in ['sidebar', 'disc-logo', 'shifted-column']:
    target = root / 'out/visual/start-negative' / mutation
    target.mkdir(parents=True, exist_ok=True)
    expected = set()
    for original in sorted(actual.glob('*.ppm')):
        im = Image.open(original).convert('RGB')
        panel = im.getpixel((2, im.height - 2))
        draw = ImageDraw.Draw(im)
        x0, y0, x1, y1 = lockup_box(im)
        if mutation == 'sidebar':
            if im.width < 720:
                continue  # phones have no sidebar to add
            draw.rectangle((0, 0, 219, im.height - 1), fill=(0x76, 0x47, 0xc7))
        elif mutation == 'disc-logo':
            # the old wordmark: a disc, then the name in small type
            draw.rectangle((x0, y0, x1, y1), fill=panel)
            d = y1 - y0
            draw.ellipse((x0, y0, x0 + d, y1), fill=(0x76, 0x47, 0xc7))
        else:
            column = im.crop((0, y0 - 4, im.width, im.height))
            im.paste(Image.new('RGB', im.size, panel))
            im.paste(column, (0, y0 - 4 + max(8, im.height // 100)))
        im.save(target / original.name)
        expected.add(original.stem)
    for case in set(budgets) - expected:
        (target / f'{case}.ppm').unlink(missing_ok=True)
    trimmed = {k: v for k, v in budgets.items() if k in expected}
    staged = target / 'reference'
    shutil.rmtree(staged, ignore_errors=True)
    staged.mkdir()
    for case in expected:
        shutil.copyfile(reference / f'{case}.png', staged / f'{case}.png')
    _, failures = compare(staged, target, target / 'report', trimmed)
    rejected = {f.split(':')[0] for f in failures}
    assert expected <= rejected, (mutation, 'mutation escaped', expected - rejected)
    print(f'get started: {mutation} rejected in {len(expected)} cases')
