#!/usr/bin/env python3
"""Pin the variable sources, instance Regular (400), then subset for shipping."""
import argparse
import hashlib
import json
from pathlib import Path
from fontTools import subset
from fontTools.ttLib import TTFont
from fontTools.varLib.instancer import instantiateVariableFont
from cjk_sets import coverage

ROOT = Path(__file__).resolve().parents[1]

def build(source, dest, manifest):
    dest.mkdir(parents=True, exist_ok=True)
    records = []
    for line in (ROOT/'tools/cjk_fonts.tsv').read_text().splitlines():
        digest, name, url = line.split()
        path = source/name
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f'{name}: source hash mismatch')
        locale = name[8:10]
        f = TTFont(path, recalcTimestamp=False)
        f = instantiateVariableFont(f, {'wght': 400}, inplace=True, updateFontNames=True)
        if 'fvar' in f or f['OS/2'].usWeightClass != 400 or 'Thin' in f['name'].getDebugName(1):
            raise ValueError(f'{name}: not static Regular')
        requested = coverage()[locale]
        expected = requested & set(f.getBestCmap())
        # Instance first: dropping gvar before this would silently ship Thin.
        for tag in ['fvar','gvar','HVAR','VVAR','MVAR','avar','STAT','cvar','GSUB','GPOS','GDEF','BASE','JSTF','DSIG']:
            if tag in f:
                del f[tag]
        opts = subset.Options()
        opts.hinting = False
        opts.layout_features = []
        opts.name_IDs = [0,1,2,3,4,5,6,13,14]
        opts.recalc_timestamp = False
        sub = subset.Subsetter(options=opts)
        sub.populate(unicodes=sorted(expected))
        sub.subset(f)
        if set(f.getBestCmap()) != expected:
            raise ValueError(f'{name}: subset coverage changed')
        target = dest/f'NotoSans{locale}-Common.ttf'
        f.save(target, reorderTables=True)
        records.append(dict(locale=locale, weight=400, source=name, url=url, source_sha256=digest,
            requested=len(requested), mapped=len(expected), glyphs=f['maxp'].numGlyphs,
            bytes=target.stat().st_size, sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
            missing=[f'{c:04X}' for c in sorted(requested-expected)]))
        print(f'{locale}: {len(expected)} characters, {target.stat().st_size} bytes', flush=True)
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--fonts',type=Path,default=Path('/mnt/storage/holmes-wt/lq-tonight/fonts'))
    p.add_argument('--out',type=Path,default=ROOT/'assets')
    p.add_argument('--manifest',type=Path,default=ROOT/'out/cjk/manifest.json')
    a=p.parse_args()
    build(a.fonts,a.out,a.manifest)
