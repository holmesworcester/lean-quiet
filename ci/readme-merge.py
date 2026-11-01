#!/usr/bin/env python3
"""Resolve README.md's merge conflicts when every conflicting line on both
sides is generated (a theorem link `[name]: path#L..` or a table row
`| ...`): main's side is taken, and ci/proof-links.py writes them again
after the build. Any other conflict is left as it is; exit 1 then."""
import re, sys
p = 'README.md'
s = open(p).read()
hunk = re.compile(r'<<<<<<< [^\n]*\n(.*?)(?:\|\|\|\|\|\|\| [^\n]*\n.*?)?=======\n(.*?)>>>>>>> [^\n]*\n', re.S)
generated = re.compile(r'^(\[[^\]]+\]: \S+|\|.*)$')
ok = True
def resolve(m):
    global ok
    ours, theirs = m.group(1), m.group(2)
    if all(generated.match(l) for side in (ours, theirs) for l in side.split('\n') if l):
        return theirs
    ok = False
    return m.group(0)
s = hunk.sub(resolve, s)
open(p, 'w').write(s)
sys.exit(0 if ok and '<<<<<<<' not in s else 1)
