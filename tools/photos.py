#!/usr/bin/env python3
"""Scale the sample photos to QOI: assets/0.qoi to assets/5.qoi.

    photos.py ORIGINALS_DIR ASSETS_DIR

ORIGINALS_DIR holds <index>.jpg for each row of tools/photos.tsv, already
checked against its sha256 (tools/fetch_assets.sh). Each is turned upright
by its EXIF orientation, made RGB, scaled with Lanczos to fit its box with
its aspect kept, and written as QOI. With the pinned Pillow (12.1.1, whose
wheel carries its own libjpeg-turbo) the output is the same bytes every
time; tools/photos.sha256 pins it.
"""
from pathlib import Path
import sys

from PIL import Image, ImageOps

ROOT = Path(__file__).resolve().parents[1]


def rows():
    for line in (ROOT / 'tools/photos.tsv').read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            index, _sha, box, _url = line.split('\t')
            w, h = (int(n) for n in box.split('x'))
            yield int(index), w, h


def main(src: Path, dst: Path) -> None:
    dst.mkdir(parents=True, exist_ok=True)
    for i, bw, bh in rows():
        with Image.open(src / f'{i}.jpg') as im:
            im = ImageOps.exif_transpose(im).convert('RGB')
            scale = min(bw / im.width, bh / im.height, 1)
            size = (max(1, round(im.width * scale)), max(1, round(im.height * scale)))
            out = im.resize(size, Image.Resampling.LANCZOS)
        out.save(dst / f'{i}.qoi', 'QOI')
        print(f'photo {i}: {size[0]}x{size[1]}, {(dst / f"{i}.qoi").stat().st_size} bytes')


if __name__ == '__main__':
    main(Path(sys.argv[1]), Path(sys.argv[2]))
