"""Reproducible common sets from Python's standard character-code mappings.

SC: GB 2312-1980 level 1, zones 16..55 (3755 Han).
TC: Big5 first/common level, A440..C67E (5401 Han).
JP: JIS X 0208 level 1, rows 16..47 (2965 kanji), plus kana.
KR: KS X 1001 Hangul (2350) and Hanja (4888).
The codecs are local CPython mappings, checked by cardinality; no web data.
"""
from pathlib import Path


def decode_grid(codec, leads, trails, accept=lambda a, b: True):
    result = set()
    for a in leads:
        for b in trails:
            if not accept(a, b):
                continue
            try:
                s = bytes((a,b)).decode(codec)
            except UnicodeDecodeError:
                continue
            if len(s) == 1:
                result.add(ord(s))
    return result


def coverage():
    sc = decode_grid('gb2312', range(0xB0,0xD8), range(0xA1,0xFF))
    tc = decode_grid('big5', range(0xA4,0xC7), [*range(0x40,0x7F),*range(0xA1,0xFF)], lambda a,b: a<0xC6 or b<=0x7E)
    jp = decode_grid('euc_jp', range(0xB0,0xD0), range(0xA1,0xFF))
    hangul = decode_grid('euc_kr', range(0xB0,0xC9), range(0xA1,0xFF))
    hanja = decode_grid('euc_kr', range(0xCA,0xFE), range(0xA1,0xFF))
    assert tuple(map(len,(sc,tc,jp,hangul,hanja))) == (3755,5401,2965,2350,4888)
    punctuation = set(range(0x3000,0x3040)) | set(range(0xFF00,0xFFF0))
    return {
        'SC': sc | punctuation,
        'TC': tc | punctuation | set(range(0x3100,0x3130)) | set(range(0x31A0,0x31C0)),
        'JP': jp | punctuation | set(range(0x3040,0x3100)) | set(range(0x31F0,0x3200)),
        'KR': hangul | hanja | punctuation | set(range(0x3130,0x3190)),
    }


def corpus(out):
    sets = coverage()
    # Sample the common repertoires, interleaved by locale, in signed posts.
    pools = [sorted(v - set(range(0xFF00,0xFFF0)) - set(range(0x3000,0x3040))) for v in sets.values()]
    lines = []
    for i in range(500):
        p = pools[i % 4]
        lines.append(''.join(chr(p[(i//4*48+j) % len(p)]) for j in range(48)))
    Path(out).write_text('\n'.join(lines)+'\n')

if __name__ == '__main__':
    import sys
    corpus(sys.argv[1])
