#!/usr/bin/env python3
"""Pixel comparison with pinned libquiet CSS, without a browser or network."""
from pathlib import Path
import re
import subprocess

ref = Path('tests/app/theme-reference')
tokens = (ref / 'design-tokens.css').read_text()
roles = (ref / 'design-theme.css').read_text()
def declarations(css, dark):
    block = css.split(':root[data-theme="dark"] {')[1] if dark else css.split(':root {', 1)[1].split('}', 1)[0]
    return dict(re.findall(r'--([\w-]+):\s*([^;]+);', block))

def palette(dark):
    values = declarations(tokens, False) | declarations(roles, False)
    if dark:
        values |= declarations(tokens, True) | declarations(roles, True)
    def resolve(name):
        value = values[name]
        if value.startswith('var('): return resolve(value[6:-1])
        return int(value.removeprefix('#'), 16)
    return resolve

# Extra semantic aliases use existing libquiet primitives. The badge uses the
# text-safe brand red; its hot-pink token and avatar fills are not contrast proofs.
aliases = dict(danger='color-red', online='ink-lan', selected='gray-06', toast='panel',
               **{'toast-ink':'fg', 'edge':'fg', 'badge':'color-red', 'badge-ink':'on-accent', 'avatar':'color-purple'})
lines = subprocess.check_output(['.lake/build/bin/appearance','palette','out/appearance'], text=True).splitlines()
avatar = re.findall(r'"(#[0-9a-f]{6})"', (ref/'avatar.ts').read_text().split('AVATAR_COLORS = [')[1].split(']')[0])
expected = bytearray()
for line in lines:
    theme, name, actual = line.split()
    resolve = palette(theme == 'dark')
    if re.fullmatch(r'avatar[0-7]', name): want = int(avatar[int(name[-1])][1:],16)
    elif name in ('black','scrim'): want = 0
    elif name == 'white': want = 0xffffff
    elif name in ('danger','badge'): want = palette(False)('color-red')
    else: want = resolve(aliases.get(name,name))
    assert int(actual) == want, (theme,name,actual,hex(want))
    expected += want.to_bytes(3,'big')
ppm = Path('out/appearance/palette.ppm').read_bytes().split(b'\n',3)[3]
assert ppm == expected
print(f'libquiet palette: {len(lines)} exact RGB pixel comparisons pass')
