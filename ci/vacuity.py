#!/usr/bin/env python3
"""Inventory README proof references; never infer a witness from a theorem's existence.
Run --write to refresh the report, otherwise reject a stale report.
"""
import argparse
import json
import re
from pathlib import Path

TOP = Path(__file__).resolve().parents[1]
BEGIN = '<!-- vacuity:begin -->'
END = '<!-- vacuity:end -->'
def load_checks(directory=TOP / 'tests/vacuity'):
    checks = {}
    for path in sorted(directory.glob('*-report.json')):
        for name, entry in json.loads(path.read_text()).items():
            if name in checks:
                raise ValueError(f'duplicate vacuity evidence: {name}')
            if entry['status'] not in {'kernel-witness', 'runtime-witness', 'conditional', 'counterexample'}:
                raise ValueError(f'unknown evidence status: {name}')
            checks[name] = entry
    return checks


CHECKS = load_checks()


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
    counts = {status: sum(e['status'] == status for e in CHECKS.values())
              for status in ['kernel-witness', 'runtime-witness', 'conditional', 'counterexample']}
    rows = []
    for name, target in refs.items():
        if name in CHECKS:
            e = CHECKS[name]
            path = e['module'].replace('.', '/') + '.lean'
            status = f"**{e['status']}**: [{e['witness']}]({path}). {e['detail']}"
        else:
            status = 'Pending: no concrete premise witness audited yet'
        rows.append(f'| [`{name}`]({target}) | {status} |')
    return f"""{BEGIN}
## Vacuity check reports

Work follows the theorem columns in **Security proofs**, then **Quality proofs**,
in their README order. Repeated declarations appear once; assumptions and other
supporting references follow. This is the order for the remaining work too.

**Coverage: {counts['kernel-witness']} kernel witnesses, {counts['runtime-witness']} runtime witnesses,
{counts['conditional']} conditional checks, {counts['counterexample']} failed production assumptions; {len(refs) - len(CHECKS)} of {len(refs)} linked declarations still pending.**
A pending or conditional entry is not counted as a passed vacuity check.

**Finding: the production suites do not satisfy `Seal.Good` and Noise
`Suite.Good` as written.** Their contracts demand roundtrips for keys (and seal
nonces) of every length; the native implementations reject invalid lengths.
Runtime counterexamples demonstrate both contradictions. Valid-size roundtrips
pass. Theorems requiring these contracts, including `openSealed_seal`,
`member_opens`, `unbox_box` and the affected handshake/frame laws, need
size-aware contracts before their assumptions apply to the production suites.
These are specification/applicability gaps, not demonstrated breaks of
valid-size encryption.

- **kernel-witness:** Lean checks a concrete fixture's premises and application
  of the named theorem. No new axioms, `sorry`, or `native_decide` are admitted.
- **runtime-witness:** native crypto or rendering code executes; a successful decidable
  branch constructs the premise and applies the theorem. The executable checks
  success. This trusts Lean's compiler and native functions, beyond the kernel.
- **counterexample:** a concrete production input contradicts the named assumption.
- **conditional:** a required assumption remains open and is named explicitly.
  A finite set of good signatures cannot prove Ed25519 unforgeability.

**Provenance:** all current fixtures are synthetic. The identity fixture uses
actual Ed25519 signatures and the production validators. Sync fixtures use
nonempty chat payloads on a generic held store, with their limits stated per row.
No real-user community transcript has been captured or claimed as checked.

Run `mise run test:vacuity`; local CI invokes the same task through
`ci/local.sh vacuity` and retains its log at `out/ci/vacuity.log`. It builds the
fixture dependencies, checks kernel witnesses and their theorem dependencies,
runs the native fixtures, checks negative controls, and verifies this ordered
inventory. The task requires the repository's native crypto/build prerequisites
and font assets (asset scripts prepare missing fonts); logs are retained under
`out/vacuity`. Native panics or timeouts fail the run even if the process otherwise
returns success. The dependency/axiom gate checks evidence structure; manual
fixture review checks that the examples actually inhabit their premises and
that runtime certificates are asserted. Neither theorem existence nor dependency
reachability alone establishes nonvacuity.

### Checks in README order

| Declaration | Evidence / remaining work |
|---|---|
""" + '\n'.join(rows) + f"""

### How to read the evidence

For image sizing, the 4032 × 3024 photo and edge 2048 satisfy `fit_long`'s two
premises by computation. Applying that theorem gives longer output side 2048;
a separate exact-result check requires `(2048, 1536)`. Portrait, thumbnail,
rounding and one-pixel-clamp cases exercise other branches; false premises and
incorrect output variants are rejected.

For identity, the fixture creates Alice and Bob, an invitation, a signed join
request, approval, admission, messages, an admin grant and opposing removals.
Successful runtime validity checks construct the corresponding theorem premises.
Forgery and invalid approval controls must fail. This does not discharge the
universal `Unforgeable` hypothesis of `no_impersonation`.

For encoding and ordering, fixed nonempty wire bytes, malformed trailing bytes,
three interleaved message rows and a two-row query limit check concrete behavior.
The op hash remains symbolic in kernel proofs; no collision-freedom claim is made.

These are evidence of inhabited premises and meaningful consequences at the
stated boundary, not proofs of every native adapter or full user session.
{END}
"""


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
    print(f'vacuity inventory: {len(CHECKS)} evidence entries / {len(references(text))} linked declarations')


if __name__ == '__main__':
    main()
