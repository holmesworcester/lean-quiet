#!/usr/bin/env python3
"""Compare Lean with the original variable fonts instanced at Regular (wght 400).
Also verify every subset cmap/metric and actual Text/Paint line pixels.
Uses the first pass's independent fontTools pen and sampled fill.
"""
import sys
import math
import hashlib
import os
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'tools'))
from fontTools.ttLib import TTFont
from fontTools.varLib.instancer import instantiateVariableFont
from fontTools import version as fonttools_version
from cjk_sets import coverage, corpus
from noto_reference import Pen, draw, reference

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'out/cjk'
SOURCE=Path(os.environ.get('CJK_FONTS','/mnt/storage/holmes-wt/lq-tonight/fonts'))
SAMPLES={
 'SC':'我们明天在图书馆见面，讨论新的计划。',
 'TC':'我們明天在圖書館見面，討論新的計畫。',
 'JP':'今日は図書館で新しい計画を話します。',
 'KR':'오늘 도서관에서 새로운 계획을 이야기합니다.',
}

def regular(locale):
 path=SOURCE/f'NotoSans{locale}-wght.ttf'
 stamp=hashlib.sha256(path.read_bytes()).hexdigest()+':400:'+fonttools_version
 dest=OUT/f'Original{locale}-Regular.ttf'
 tag=dest.with_suffix('.stamp')
 if not dest.exists() or not tag.exists() or tag.read_text()!=stamp:
  f=instantiateVariableFont(TTFont(path,recalcTimestamp=False),{'wght':400},inplace=True)
  f.save(dest);tag.write_text(stamp)
 f=TTFont(dest)
 assert 'fvar' not in f and f['OS/2'].usWeightClass==400
 return f

def prepare():
 OUT.mkdir(parents=True,exist_ok=True)
 corpus(OUT/'corpus.txt')
 for locale, chars in SAMPLES.items():
  name=f'NotoSans{locale}-Common'
  f=TTFont(ROOT/'assets'/f'{name}.ttf')
  original=regular(locale)
  assert f['OS/2'].usWeightClass==400
  mapping=f.getBestCmap()
  assert set(mapping)==coverage()[locale]&set(original.getBestCmap())
  assert not {'fvar','gvar','HVAR'} & set(f.keys())
  for cp,g in mapping.items():
   assert f['hmtx'][g] == original['hmtx'][original.getBestCmap()[cp]], (locale,cp,'metrics changed')
  (OUT/f'{name}.map').write_text(''.join(f'{cp} {f.getGlyphID(g)} {f["hmtx"][g][0]}\n' for cp,g in sorted(mapping.items())))
  # Script samples plus a deterministic spread across each complete repertoire.
  points=(set(map(ord,chars)) | set(sorted(mapping)[::max(1,len(mapping)//24)]))&set(mapping)
  (OUT/f'{name}.samples').write_text(''.join(f'{cp} {size}\n' for cp in sorted(points) for size in (16,32,48,64)))
 (OUT/'lines.txt').write_text('\n'.join(SAMPLES.values())+'\n')

def compare():
 worst=0; total=0; error=0; pixels=0
 for locale in SAMPLES:
  name=f'NotoSans{locale}-Common'
  f=regular(locale)
  gs=f.getGlyphSet()
  for line in (OUT/f'{name}.samples').read_text().splitlines():
   cp,size=map(int,line.split()); stem=OUT/f'{name}-{cp}-{size}'
   x,y,w,h,advance=map(int,stem.with_suffix('.box').read_text().split())
   glyph=f.getBestCmap()[cp]
   assert advance==(f['hmtx'][glyph][0]*size+f['head'].unitsPerEm//2)//f['head'].unitsPerEm
   pen=Pen(gs,size/f['head'].unitsPerEm,size*4//5); draw(f,gs,glyph,pen)
   expected=reference(pen.edges,x,y,w,h)
   actual=stem.with_suffix('.pgm').read_bytes().split(b'\n',3)[3]
   assert len(actual)==len(expected)
   delta=[abs(a-b) for a,b in zip(actual,expected)]
   maximum=max(delta,default=0); mean=sum(delta)/max(1,len(delta))
   assert maximum<=32 and mean<=1,(locale,cp,size,maximum,mean)
   worst=max(worst,maximum);error+=sum(delta);pixels+=len(delta);total+=1
 # Same routed fonts and placements as Text; all RGB channels are checked.
 width,height=1500,390
 canvas=bytearray([255])*(width*height)
 fonts={}
 for row in (OUT/'scripts.layout').read_text().splitlines():
  name,gid,size,x,y=row.split();gid,size,x,y=map(int,(gid,size,x,y))
  if name not in fonts: fonts[name]=TTFont(ROOT/'assets'/f'{name}.ttf')
  f=fonts[name];gs=f.getGlyphSet();pen=Pen(gs,size/f['head'].unitsPerEm,size*4//5)
  draw(f,gs,f.getGlyphName(gid),pen)
  if not pen.edges:continue
  x0=math.floor(min(min(e[0],e[2]) for e in pen.edges));y0=math.floor(min(min(e[1],e[3]) for e in pen.edges))
  w=math.ceil(max(max(e[0],e[2]) for e in pen.edges))-x0;h=math.ceil(max(max(e[1],e[3]) for e in pen.edges))-y0
  ref=reference(pen.edges,x0,y0,w,h)
  for gy in range(h):
   for gx in range(w):
    px,py=x+x0+gx,y+y0+gy
    if 0<=px<width and 0<=py<height:
     a=ref[gy*w+gx];at=py*width+px
     canvas[at]=(20*a+canvas[at]*(255-a)+127)//255
 actual=(OUT/'scripts.ppm').read_bytes().split(b'\n',3)[3]
 assert len(actual)==3*len(canvas)
 delta=[abs(canvas[i//3]-v) for i,v in enumerate(actual)]
 assert max(delta)<=32 and sum(delta)/len(delta)<=1,('line pixels',max(delta))
 print(f'CJK reference: {total} bitmaps, {pixels} pixels, max {worst}/255, mean {error/pixels:.5f}/255; 4 routed lines, {len(canvas)} pixels, max {max(delta)}/255; tolerance 32 max / 1 mean')

if __name__=='__main__':{'prepare':prepare,'compare':compare}[sys.argv[1]]()
