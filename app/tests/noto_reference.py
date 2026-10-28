#!/usr/bin/env python3
"""Offline fontTools reference: cmap/hmtx plus a BasePen quadratic raster.

The reference subdivides each quadratic into 128 chords (independently of
Lean's adaptive subdivision), fills by nonzero winding at 8x8 sample centres,
and compares every pixel with tolerance 32/255 and mean error <= 1/255.
No native rasterizer supplies application pixels. All outputs live in out/.
"""
import importlib.util
import math
from pathlib import Path
import struct
import sys

if importlib.util.find_spec('fontTools') is None:
    for root in [Path('/mnt/storage/holmes-tmp/pylib'), *Path.home().glob('.local/lib/python*/site-packages')]:
        if (root / 'fontTools').is_dir():
            sys.path.insert(0, str(root))
            break
from fontTools.ttLib import TTFont
from fontTools.pens.basePen import BasePen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.fontBuilder import FontBuilder
from fontTools.ttLib.tables._g_l_y_f import Glyph, GlyphComponent

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(sys.argv[2] if len(sys.argv) > 2 else ROOT / 'out/noto')
SAMPLES = {
    'NotoSans': 'Quiet café Ångström naïve AV Wi Ελληνικά Καλημέρα Привет мир',
    'NotoSansArmenian': 'Բարեւ աշխարհ',
    'NotoSansGeorgian': 'გამარჯობა მსოფლიო',
    'NotoSansHebrew': 'שלום עולם שָׁלוֹם',
    'NotoSansArabic': 'ﺍﻟﺴﻼﻡ ﻋﻠﻴﻜﻢ ﻣﺮﺣﺒﺎ',
    'NotoSansThai': 'สวัสดี โลก ภาษาไทย',
    'NotoSansEthiopic': 'ሰላም ዓለም',
    'NotoSansCherokee': 'ᎣᏏᏲ ᏣᎳᎩ',
    'NotoSansCanadianAboriginal': 'ᐊᐃᓐᓇᐃ ᐃᓄᒃᑎᑐᑦ',
    'Transforms': 'ABCDE',
}
SIZES = (16, 32, 48)

def font(name):
    return TTFont((OUT / 'Transforms.ttf') if name == 'Transforms' else ROOT / 'assets' / (name + '-Regular.ttf'), recalcBBoxes=False)

def transforms():
    # A real sfnt containing each composite transform, plus point attachment.
    fb = FontBuilder(1000, isTTF=True)
    order = ['.notdef','base','scale','stretch','matrix','attach']
    fb.setupGlyphOrder(order)
    glyphs = {}
    p = TTGlyphPen(None)
    glyphs['.notdef'] = p.glyph()
    p = TTGlyphPen(None)
    p.moveTo((0,0)); p.lineTo((400,0)); p.qCurveTo((500,400),(200,700)); p.lineTo((0,0)); p.closePath()
    glyphs['base'] = p.glyph()
    for name, transform in [('scale',(.75,0,0,.75,100,50)),('stretch',(1.25,0,0,.5,0,0)),('matrix',(1,.25,-.125,1,20,15))]:
        p = TTGlyphPen(glyphs)
        p.addComponent('base', transform)
        glyphs[name] = p.glyph()
    attached = Glyph()
    attached.numberOfContours = -1
    one = GlyphComponent(); one.glyphName = 'base'; one.x = one.y = 0; one.flags = 0
    two = GlyphComponent(); two.glyphName = 'base'; two.firstPt = 1; two.secondPt = 0; two.flags = 0
    attached.components = [one,two]
    glyphs['attach'] = attached
    fb.setupGlyf(glyphs)
    fb.setupHorizontalMetrics({name:(1000,0) for name in order})
    fb.setupHorizontalHeader(ascent=800,descent=-200)
    fb.setupCharacterMap({65+i:name for i,name in enumerate(order[1:])})
    fb.setupNameTable({'familyName':'Quiet test','styleName':'Regular'})
    fb.setupOS2(); fb.setupPost(); fb.setupMaxp()
    fb.save(OUT / 'Transforms.ttf')

def prepare():
    OUT.mkdir(parents=True, exist_ok=True)
    transforms()
    for name, text in SAMPLES.items():
        f = font(name)
        assert 'fvar' not in f and f['OS/2'].usWeightClass == 400, (name, 'not static Regular')
        cmap = f.getBestCmap()
        (OUT / (name + '.map')).write_text(''.join(f'{cp} {f.getGlyphID(g)} {f["hmtx"][g][0]}\n' for cp, g in sorted(cmap.items())))
        (OUT / (name + '.samples')).write_text(''.join(f'{cp} {size}\n' for cp in sorted(set(map(ord, text))) if cp in cmap for size in SIZES))
    (OUT / 'lines.txt').write_text('\n'.join([
        'Quiet café Ångström — AV Wi', 'Ελληνικά Καλημέρα', 'Привет мир',
        SAMPLES['NotoSansArmenian'], SAMPLES['NotoSansGeorgian'], SAMPLES['NotoSansHebrew'],
        'السلام عليكم مرحبا', SAMPLES['NotoSansThai'], SAMPLES['NotoSansEthiopic'],
        SAMPLES['NotoSansCherokee'], SAMPLES['NotoSansCanadianAboriginal'],
        'Fallback: 漢字 日本語 हिन्दी', 'Emoji: 😀 🎉 ❤️',
    ]))
    raw = (ROOT / 'assets/NotoSans-Regular.ttf').read_bytes()
    f = font('NotoSans')
    cuts = set(range(0, 256)) | {len(raw)-1}
    for tag in f.reader.tables.values():
        cuts.update([tag.offset, tag.offset + tag.length - 1])
    hostile = []
    def save(name, data):
        (OUT / name).write_bytes(data)
        hostile.append(name)
    for i, cut in enumerate(sorted(cuts)):
        save(f'truncated-{i}.ttf', raw[:cut])
    for k in range(struct.unpack_from('>H', raw, 4)[0]):
        bad = bytearray(raw)
        struct.pack_into('>I', bad, 12 + k*16 + 8, 0xfffffff0)
        save(f'offset-{k}.ttf', bad)
    glyf = f.reader.tables['glyf'].offset
    for gid, name in enumerate(f.getGlyphOrder()):
        if f['glyf'][name].isComposite():
            bad = bytearray(raw)
            struct.pack_into('>H', bad, glyf + f['loca'][gid] + 12, gid)
            save('composite-loop.ttf', bad)
            # Also truncate the first component by corrupting its loca end.
            break
    # Standalone cmap fixtures exercise format 4's glyph-array + delta and
    # format 12's supplementary planes. These need no installed font changes.
    sub4 = struct.pack('>7H', 4, 38, 0, 4, 4, 1, 0)
    sub4 += struct.pack('>2H', 66, 65535) + b'\0\0'
    sub4 += struct.pack('>2H', 65, 65535) + struct.pack('>2h', -2, 1)
    sub4 += struct.pack('>2H', 4, 0) + struct.pack('>3H', 7, 0, 0)
    sub12 = struct.pack('>HHIII', 12, 0, 28, 0, 1) + struct.pack('>III', 0x10000, 0x10002, 9)
    for name, sub in [('format4', sub4), ('format12', sub12)]:
        (OUT / (name + '.cmap')).write_bytes(struct.pack('>HHHHI', 0, 1, 3, 10 if name == 'format12' else 1, 12) + sub)
    (OUT / 'hostile.txt').write_text('\n'.join(hostile))
    print(f'reference prepared: {len(hostile)} hostile fixtures, 9 fonts, 3 sizes')

class Pen(BasePen):
    def __init__(self, glyphs, scale, baseline):
        super().__init__(glyphs)
        self.scale, self.baseline = scale, baseline
        self.edges = []
    def pixel(self, p):
        return p[0]*self.scale, self.baseline-p[1]*self.scale
    def _moveTo(self, p):
        self.start = self.last = self.pixel(p)
    def _lineTo(self, p):
        p = self.pixel(p)
        self.edges.append((*self.last, *p))
        self.last = p
    def _qCurveToOne(self, b, c):
        a, b, c = self.last, self.pixel(b), self.pixel(c)
        for i in range(1, 129):
            t = i/128
            u = 1-t
            p = (u*u*a[0] + 2*u*t*b[0] + t*t*c[0], u*u*a[1] + 2*u*t*b[1] + t*t*c[1])
            self.edges.append((*self.last, *p))
            self.last = p
    def _closePath(self):
        self.edges.append((*self.last, *self.start))
        self.last = self.start
    def _endPath(self):
        self._closePath()

def draw(f, glyphs, name, pen):
    g = f['glyf'][name]
    if g.isComposite() and any(hasattr(c, 'firstPt') for c in g.components):
        # BasePen cannot consume TrueType point attachments directly;
        # fontTools resolves those into coordinates before the same pen.
        flat = Glyph()
        flat.coordinates, flat.endPtsOfContours, flat.flags = g.getCoordinates(f['glyf'])
        flat.numberOfContours = len(flat.endPtsOfContours)
        flat.draw(pen, f['glyf'])
    else:
        glyphs[name].draw(pen)

def reference(edges, x0, y0, w, h):
    counts = [0]*(w*h)
    for row in range(h):
        for sy in range(8):
            y = y0+row+(sy+.5)/8
            crossings = sorted((ax+(y-ay)*(bx-ax)/(by-ay), 1 if by>ay else -1)
                for ax,ay,bx,by in edges if ay<=y<by or by<=y<ay)
            winding, left = 0, 0
            for x, direction in crossings:
                if winding:
                    a = max(0, math.ceil((left-x0)*8-.5))
                    b = min(w*8, math.ceil((x-x0)*8-.5))
                    for sx in range(a,b):
                        counts[row*w+sx//8] += 1
                winding += direction
                left = x
    return bytes(min(255,n*255//64) for n in counts)

def compare():
    total, worst, errors, pixels = 0, 0, 0, 0
    for name, text in SAMPLES.items():
        f = font(name)
        glyphs = f.getGlyphSet()
        for line in (OUT / (name+'.samples')).read_text().splitlines():
            cp,size = map(int,line.split())
            stem = OUT / f'{name}-{cp}-{size}'
            x,y,w,h,advance = map(int,stem.with_suffix('.box').read_text().split())
            gname = f.getBestCmap()[cp]
            expected_advance = (f['hmtx'][gname][0]*size+f['head'].unitsPerEm//2)//f['head'].unitsPerEm
            assert advance == expected_advance, (name,cp,size,'advance')
            pen = Pen(glyphs,size/f['head'].unitsPerEm,size*4//5)
            draw(f,glyphs,gname,pen)
            ref = reference(pen.edges,x,y,w,h)
            got = stem.with_suffix('.pgm').read_bytes().split(b'\n',3)[3]
            assert len(got) == w*h
            diff = [abs(a-b) for a,b in zip(got,ref)]
            maximum = max(diff,default=0)
            mean = sum(diff)/max(1,len(diff))
            if maximum > 32 or mean > 1:
                raise AssertionError((name,chr(cp),cp,size,maximum,mean))
            worst = max(worst,maximum)
            errors += sum(diff)
            pixels += len(diff)
            total += 1
    # Compare the app's Paint/Text line sheet as well as isolated glyphs.
    width, height = 1100, 1010
    canvas = bytearray([255])*(width*height)
    fonts = {name: font(name) for name in SAMPLES}
    for line in (OUT / 'scripts.layout').read_text().splitlines():
        name,gid,size,x,y = line.split()
        gid,size,x,y = map(int,(gid,size,x,y))
        f = fonts[name]
        glyphs = f.getGlyphSet()
        pen = Pen(glyphs,size/f['head'].unitsPerEm,size*4//5)
        draw(f,glyphs,f.getGlyphName(gid),pen)
        if not pen.edges:
            continue
        x0 = math.floor(min(min(e[0],e[2]) for e in pen.edges))
        y0 = math.floor(min(min(e[1],e[3]) for e in pen.edges))
        w = math.ceil(max(max(e[0],e[2]) for e in pen.edges))-x0
        h = math.ceil(max(max(e[1],e[3]) for e in pen.edges))-y0
        ref = reference(pen.edges,x0,y0,w,h)
        for gy in range(h):
            for gx in range(w):
                px,py = x+x0+gx,y+y0+gy
                if 0<=px<width and 0<=py<height:
                    a = ref[gy*w+gx]
                    at = py*width+px
                    canvas[at] = (20*a+canvas[at]*(255-a)+127)//255
    actual = (OUT / 'scripts-core.ppm').read_bytes().split(b'\n',3)[3][:width*height*3]
    differences = [abs(canvas[i//3]-value) for i,value in enumerate(actual)]
    assert len(actual) == 3*len(canvas)
    assert max(differences)<=32 and sum(differences)/len(differences)<=1, ('line paint',max(differences))
    print(f'fontTools line reference: 11 script lines, {len(canvas)} pixels, max error {max(differences)}/255')
    print(f'fontTools reference: {total} bitmaps, {pixels} pixels; max error {worst}/255, mean {errors/max(1,pixels):.4f}/255; tolerance 32 max, 1 mean')

if __name__ == '__main__':
    {'prepare':prepare, 'compare':compare}[sys.argv[1]]()
