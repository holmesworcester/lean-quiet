#!/usr/bin/env python3
"""The app's data (assets/) as one pinned tarball, for `make install`.

  assets.py pack [--assets DIR] [--out DIR] [--against-pin] [--manifest F] [--pin F]
      Pack DIR (default assets/) into out/make/lean-quiet-assets-<id>.tar.gz
      with fixed order, times, owners and modes, so the same files always
      give the same bytes. Write the per-file list (tools/make/assets.sha256)
      and the pin (tools/make/assets.pin), and print the tarball's sha256.
      With --against-pin, write neither: fail unless the tarball's sha256 is
      the pinned one (the clean-room test packs what it serves this way).
  assets.py check [--manifest FILE] [--pin FILE]
      Check that the per-file list still matches this tree: the hashes the
      asset scripts pin (tools/*.sha256), the stamps glyph_assets.py and
      ui_fonts.py compare, the copied sources, and the scripts that make
      font.bin, emoji.bin and the photos. If a change to the tree makes the
      published tarball stale, this fails: pack again and publish. The
      notice and licence texts (tools/third_party) and the photos
      (tools/photos.sha256) are checked too.

Uses only the standard library. tools/make/assets.sh downloads, checks and
unpacks the tarball; this script is for whoever publishes it.
"""
import argparse
import gzip
import hashlib
from pathlib import Path
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'tools/make'
MANIFEST = HERE / 'assets.sha256'
PIN = HERE / 'assets.pin'
# The scripts that make font.bin and emoji.bin from their pinned sources.
# They write no stamp and their outputs are not pinned in the tree, so the
# pin records a digest of them. (tools/photos.sha256 pins the photos.)
MAKERS = ['tools/fetch_assets.sh', 'tools/font.py', 'tools/emoji.py']
REPO = 'holmesworcester/lean-quiet'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def makers_digest() -> str:
    return sha(b''.join(sha((ROOT / m).read_bytes()).encode() + b' ' + m.encode() + b'\n' for m in MAKERS))


def read_manifest(path: Path) -> dict:
    """sha256sum's format: '<hash>  <name>' per line."""
    out = {}
    for line in path.read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            h, name = line.split(None, 1)
            out[name.strip().lstrip('*')] = h
    return out


def read_pin(path: Path) -> dict:
    out = {}
    for line in path.read_text().splitlines():
        if '=' in line and not line.startswith('#'):
            k, v = line.split('=', 1)
            out[k.strip()] = v.strip()
    return out


def pack(src: Path, out_dir: Path, against_pin: bool, manifest: Path = MANIFEST, pin: Path = PIN) -> int:
    files = sorted(p for p in src.rglob('*') if p.is_file())
    if not files:
        sys.exit(f'assets.py: no files in {src}')
    out_dir.mkdir(parents=True, exist_ok=True)
    tmp = out_dir / 'lean-quiet-assets.tar.gz.part'
    with open(tmp, 'wb') as raw:
        # filename='' and mtime=0: no name or time in the gzip header.
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=9) as gz:
            with tarfile.open(fileobj=gz, mode='w', format=tarfile.USTAR_FORMAT) as tar:
                for p in files:
                    info = tarfile.TarInfo('assets/' + p.relative_to(src).as_posix())
                    info.size = p.stat().st_size
                    info.mtime, info.mode, info.uid, info.gid = 0, 0o644, 0, 0
                    info.uname = info.gname = ''
                    with open(p, 'rb') as f:
                        tar.addfile(info, f)
    digest = sha(tmp.read_bytes())
    ident = digest[:12]
    name = f'lean-quiet-assets-{ident}.tar.gz'
    final = out_dir / name
    tmp.replace(final)
    print(f'{final} {final.stat().st_size} bytes, {len(files)} files')
    print(f'sha256 {digest}')
    if against_pin:
        pinned = read_pin(pin).get('LQ_ASSETS_SHA256')
        if digest != pinned:
            print(f'assets.py: {src} packs to {digest}, not the pinned {pinned}', file=sys.stderr)
            return 1
        return 0
    manifest.write_text(''.join(f'{sha(p.read_bytes())}  {p.relative_to(src).as_posix()}\n' for p in files))
    pin.write_text(
        '# The app\'s data (assets/: fonts, emoji, glyphs, photos) as one tarball,\n'
        '# a GitHub release asset. Written by tools/make/assets.py pack; read by\n'
        '# tools/make/assets.sh (make install), which checks the download against\n'
        '# LQ_ASSETS_SHA256 before opening it and each file against assets.sha256.\n'
        f'LQ_ASSETS_REPO={REPO}\n'
        f'LQ_ASSETS_TAG=assets-{ident}\n'
        f'LQ_ASSETS_NAME={name}\n'
        f'LQ_ASSETS_SHA256={digest}\n'
        f'LQ_ASSETS_MAKERS={makers_digest()}\n')
    print(f'wrote {manifest} and {pin}')
    # A copy in assets/ older than its source (a NOTICE edited since the
    # last build) would be published stale: refuse it. (Made-up folders,
    # without a NOTICE, are the tests'.)
    if (src / 'NOTICE.txt').exists() and check(manifest, pin):
        print('assets.py: the packed files are not this tree\'s; run tools/noto_assets.sh '
              '(or tools/fetch_assets.sh) and pack again', file=sys.stderr)
        return 1
    return 0


def check(manifest_path: Path, pin_path: Path) -> int:
    m = read_manifest(manifest_path)
    pin = read_pin(pin_path)
    bad = []

    def want(name, expected, why):
        got = m.get(name)
        if got != expected:
            bad.append(f'{name}: the tarball has {got or "nothing"}, {why} wants {expected}')

    for list_file in ['tools/noto.sha256', 'tools/noto-index.sha256', 'tools/cjk-subsets.sha256',
                      'tools/photos.sha256']:
        for name, h in read_manifest(ROOT / list_file).items():
            want(name, h, list_file)
    copied = [('picker.txt', 'tools/third_party/picker.txt'),
              ('NOTO-LICENSE.txt', 'tools/NOTO-LICENSE.txt'),
              ('NOTICE.txt', 'tools/third_party/NOTICE.txt'),
              ('NotoSans-UI-Medium.ttf', 'ui/fonts/NotoSans-UI-Medium.ttf')]
    copied += [(p.name, p.relative_to(ROOT).as_posix())
               for p in sorted((ROOT / 'tools/third_party/licenses').glob('LICENSE-*.txt'))]
    for name, source in copied:
        want(name, sha((ROOT / source).read_bytes()), source)
    # The stamps: glyph_assets.py and ui_fonts.py rebuild their outputs (and
    # need librsvg, Cairo or fontTools) unless the stamp equals this digest.
    svgs = sorted((ROOT / 'ui/glyphs').glob('*.svg'))
    glyphs = sha((ROOT / 'tools/glyph_assets.py').read_bytes() + b''.join(p.read_bytes() for p in svgs))
    want('ui-glyphs.sha256', sha(glyphs.encode()), 'tools/glyph_assets.py and ui/glyphs/*.svg')
    ui = sha((ROOT / 'tools/ui_fonts.py').read_bytes() + (ROOT / 'ui/fonts/NotoSans-UI-Medium.ttf').read_bytes())
    want('noto-ui.sha256', sha(ui.encode()), 'tools/ui_fonts.py')
    for name in ['font.bin', 'emoji.bin', 'ui-glyphs.bin', 'noto-ui-index.bin']:
        if name not in m:
            bad.append(f'{name}: missing from the tarball')
    if pin.get('LQ_ASSETS_MAKERS') != makers_digest():
        bad.append(f'{", ".join(MAKERS)} changed since the tarball was packed '
                   f'(digest {makers_digest()}, pinned {pin.get("LQ_ASSETS_MAKERS")})')
    if not pin.get('LQ_ASSETS_NAME', '').endswith(pin.get('LQ_ASSETS_SHA256', '-')[:12] + '.tar.gz'):
        bad.append('assets.pin: the name does not carry the sha256')
    for b in bad:
        print('stale:', b, file=sys.stderr)
    if bad:
        print('The published assets tarball no longer matches this tree. Rebuild assets/ '
              '(tools/fetch_assets.sh), run tools/make/assets.py pack and publish the new tarball.',
              file=sys.stderr)
        return 1
    print(f'assets pin: {len(m)} files agree with this tree ({pin["LQ_ASSETS_NAME"]})')
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('pack')
    p.add_argument('--assets', type=Path, default=ROOT / 'assets')
    p.add_argument('--out', type=Path, default=ROOT / 'out/make')
    p.add_argument('--against-pin', action='store_true')
    p.add_argument('--manifest', type=Path, default=MANIFEST)
    p.add_argument('--pin', type=Path, default=PIN)
    c = sub.add_parser('check')
    c.add_argument('--manifest', type=Path, default=MANIFEST)
    c.add_argument('--pin', type=Path, default=PIN)
    a = ap.parse_args()
    if a.cmd == 'pack':
        return pack(a.assets, a.out, a.against_pin, a.manifest, a.pin)
    return check(a.manifest, a.pin)


if __name__ == '__main__':
    sys.exit(main())
