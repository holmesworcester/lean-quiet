#!/usr/bin/env python3
"""Inventory README proof references; never infer a witness from a theorem's existence.
Run --write to refresh the report, otherwise reject a stale report.
"""
import argparse
import re
from pathlib import Path

TOP = Path(__file__).resolve().parents[1]
BEGIN = '<!-- vacuity:begin -->'
END = '<!-- vacuity:end -->'
CHECKS = {
    'fit_small': ('small', '640 × 480, edge 2048; max ≤ edge; unchanged output'),
    'fit_le': ('bounded', '4032 × 3024, edge 2048; edge ≥ 1; output 2048 × 1536'),
    'fit_pos': ('positive', '4032 × 3024; both dimensions ≥ 1; output dimensions positive'),
    'fit_long': ('longSide', '4032 × 3024; edge ≥ 1 and edge < max; longer output side 2048'),
    'fit_round': ('rounding', '3024 × 4032, edge 2048; edge < max; shorter output side 1536'),
}


def references(text):
    # Link definitions are the canonical inventory maintained by proof-links.py.
    return dict(re.findall(r'^\[`([^`]+)`\]: (\S+)', text, re.M))


def ordered_references(text):
    """Follow the proof tables, then retain every supporting reference.

    Earlier prose and assumptions must not move ahead of the promises being
    checked. A declaration repeated in several guarantees keeps its first
    position; the generated report never becomes an ordering source itself.
    """
    source = text.split(BEGIN, 1)[0]
    refs = references(source)
    ordered = {}
    in_proofs = False
    for line in source.splitlines():
        if line.startswith('#'):
            in_proofs = line.strip() in {'### Security proofs', '### Quality proofs'}
        if not in_proofs or not line.startswith('|'):
            continue
        # The theorem column is last. References in a guarantee's explanatory
        # prose do not determine this ordering.
        theorem_cell = line.rstrip().rsplit('|', 2)[-2]
        for name in re.findall(r'\[`([^`]+)`\](?![(\[])', theorem_cell):
            if name not in refs:
                raise ValueError(f'proof table reference has no definition: {name}')
            ordered.setdefault(name, refs[name])
    for name, target in refs.items():
        ordered.setdefault(name, target)
    return ordered


def report(text):
    refs = ordered_references(text)
    missing = CHECKS.keys() - refs.keys()
    if missing:
        raise ValueError(f'checked references disappeared: {sorted(missing)}')
    rows = []
    for name, target in refs.items():
        if name in CHECKS:
            witness, detail = CHECKS[name]
            status = f'[Premises + application](tests/vacuity/Pictures.lean) (`{witness}`); {detail}'
        else:
            status = 'Pending: no concrete premise witness audited yet'
        rows.append(f'| [`{name}`]({target}) | {status} |')
    return f'''{BEGIN}
## Vacuity check reports

This audit is in progress: **{len(CHECKS)} of {len(refs)} README-linked declarations
have concrete premise witnesses checked**. Pending entries are not failures and
are not claimed checked. The inventory includes definitions/assumptions linked
by the README, which still need classification, as well as theorems.

Run `mise run test:vacuity`. CI runs that same task via `ci/local.sh`.
The task builds the imported production laws, checks the witness file with
Lean's kernel, checks its axioms, checks deliberately broken fixtures are
rejected, and rejects a stale inventory. No external services are needed.
Logs from CI stay in `out/ci/vacuity.log`.

### Batch 1 — photo sizing (2026-10-31)

**Provenance:** synthetic camera dimensions, not actual user data. No captured
community dataset was found or used in this batch. These functions take sizes,
so message contents, identities and signatures are irrelevant to these checks.

**How the check works:** for `fit_long`, instantiate width 4032, height 3024,
edge 2048; Lean proves `1 ≤ 2048` and `2048 < max 4032 3024` by computation;
apply the production theorem to conclude the longer output side is 2048.
Separately compute the complete output, `(2048, 1536)`, so a correct long
side alone cannot conceal an incorrect short side. The other four checks
follow this same premise/application/output pattern. They use the production
`Pic.fit`, imported from the renderer's sizing implementation.

**Controls:** oversized input fails the unchanged-size premise; zero edge
fails the bound's premise and produces a side above that edge; zero width
fails positivity and remains zero when already small; an already-small photo
fails the scaling premise. Portrait, landscape, thumbnail, rounding and
one-pixel-clamp cases have exact expected outputs. Deliberately false output
and premise variants must fail Lean checking.

**Interpretation:** these five theorem premises are inhabited by realistic
sizes and their conclusions constrain useful behavior. This establishes neither
native camera correctness nor end-to-end rendering. The remaining declarations
need their own fixtures, premise checks, conclusion review and runtime linkage;
a generic `#check` or a passing unrelated suite does not complete an entry.

### Complete README reference inventory

| Declaration | Evidence / remaining work |
|---|---|
''' + '\n'.join(rows) + f'\n{END}\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    path = TOP / 'README.md'
    text = path.read_text()
    block = report(text)
    if BEGIN in text:
        before, rest = text.split(BEGIN, 1)
        _, after = rest.split(END, 1)
        updated = before + block.rstrip('\n') + after
    else:
        updated = text.rstrip() + '\n\n' + block
    if args.write:
        path.write_text(updated)
    elif text != updated:
        raise SystemExit('Vacuity report stale: run python3 ci/vacuity.py --write')
    print(f'vacuity inventory: {len(CHECKS)} witnessed / {len(references(text))} linked declarations')


if __name__ == '__main__':
    main()
