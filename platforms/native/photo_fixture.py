"""A large asymmetric photo with EXIF rotation for the real OS picker suites."""
import sys
from pathlib import Path
from PIL import Image, ImageDraw
p = Path(sys.argv[1]); p.parent.mkdir(parents=True, exist_ok=True)
im = Image.new('RGB', (4096, 2048), 'white')
draw = ImageDraw.Draw(im)
for box, color in [((0, 0, 2047, 1023), '#f03030'), ((2048, 0, 4095, 1023), '#30c030'),
                   ((0, 1024, 2047, 2047), '#3060f0'), ((2048, 1024, 4095, 2047), '#f0c030')]:
    draw.rectangle(box, fill=color)
exif = Image.Exif(); exif[274] = 6  # rotate 90 degrees clockwise for display
im.save(p, quality=92, exif=exif)
print(p)
