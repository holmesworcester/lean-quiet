#!/usr/bin/env python3
"""Break each UX fix/law, require failure, restore, then rebuild the good code.

Run from app with the Lean toolchain on PATH. Do not run concurrently with
builds or edits: these controls temporarily mutate the running source.
"""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
out = root / 'out' / 'ux' / 'negative'
out.mkdir(parents=True, exist_ok=True)


def run(cmd, name):
    result = subprocess.run(cmd, cwd=root, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (out / (name + '.log')).write_text(result.stdout)
    return result


def control(name, path, old, new, cmd, expected):
    source = root / path
    good = source.read_text()
    assert good.count(old) == 1, (name, 'mutation must be unique')
    try:
        source.write_text(good.replace(old, new))
        result = run(cmd, name)
        assert result.returncode != 0 and expected in result.stdout, (name, result.stdout[-2500:])
        print('rejected ' + name, flush=True)
    finally:
        source.write_text(good)


control('pinned', 'Quiet/Anchor.lean', 'if b ≤ 4 then b else',
        'if b ≤ 4 then b + 1 else', ['lake', 'env', 'lean', 'Quiet/Anchor.lean'], 'error:')
control('anchor-restored', 'Quiet/Anchor.lean', '.map (· + off)', '.map (· + off + 1)',
        ['lake', 'env', 'lean', 'Quiet/Anchor.lean'], 'error:')
control('capture-witness', 'Quiet/Anchor.lean', 'some (k, b - y)', 'some (k, b - y + 1)',
        ['lake', 'env', 'lean', 'Quiet/Anchor.lean'], 'error:')
control('copy-exact', 'Quiet/Label.lean', ': String := text', ': String := text ++ "?"',
        ['lake', 'env', 'lean', 'Quiet/Label.lean'], 'error:')
control('line-reachable', 'Quiet/Label.lean', 'ls.extract (page * count)',
        'ls.extract (page * count + 1)', ['lake', 'env', 'lean', 'Quiet/Label.lean'], 'error:')
# Restore the original misleading green connection dot on the home avatar.
control('sessions-presence', 'Quiet/Pages.lean',
        "    let ini := String.ofList [(n.toList.headD '?').toUpper]",
        """    if _on[i]?.getD false then
      let r := dm.px 6
      let cx := dm.px 16 + d
      let cy := y + (rh + d) / 2
      b := b.round (cx - r - 2) (cy - r - 2) (cx + r + 2) (cy + r + 2) (r + 2) Row.bg
      b := b.round (cx - r) (cy - r) (cx + r) (cy + r) r 0x2EB67D
    let ini := String.ofList [(n.toList.headD '?').toUpper]""",
        ['lake', 'build', 'Quiet.UxLaws'], 'error: Quiet/UxLaws.lean:')

# These integration controls keep the helper proofs intact and disconnect
# the hook from the app. Only actual app-step tests can catch them.
def app_control(name, old, new, expected, mode=None):
    source = root / 'Quiet/App.lean'
    good = source.read_text()
    assert good.count(old) == 1
    try:
        source.write_text(good.replace(old, new))
        result = run(['lake', 'build', 'ux'], name + '-build')
        assert result.returncode == 0, result.stdout[-2500:]
        result = run(['.lake/build/bin/ux', str(out / name)] + ([mode] if mode else []), name)
        assert result.returncode != 0 and expected in result.stdout, result.stdout
        print('rejected ' + name, flush=True)
    finally:
        source.write_text(good)


app_control('arrival-hook',
            'let next := Anchor.restore offset.toNat saved (s.ids.toList.map fun p => (p.2, heightOf s p.2)) bottomPad',
            'let next := offset.toNat',
            'FAIL pending arrival keeps the visible row at the same pixel')
app_control('arrival-window', 'let limit := Anchor.grow offset.toNat s.limit s.total a.total',
            'let limit := s.limit',
            'FAIL a burst larger than the fetch window retains the visible message')
app_control('arrival-vsync', 'pure (b.toNat + next - offset.toNat)',
            'let observed ← s.io.scroll ch0.toUInt32 (viewH s).toUInt32\n    pure observed.toNat',
            'FAIL pending arrival keeps the visible row at the same pixel', mode='queued')
app_control('label-hook', 'showLabel s.me.name; return', 'pure (); return',
            'FAIL long press on the header opens its complete label')
result = run(['lake', 'build', 'ux'], 'restored-build')
assert result.returncode == 0, result.stdout[-2500:]
result = run(['.lake/build/bin/ux', str(out / 'restored')], 'restored-suite')
assert result.returncode == 0, result.stdout
result = run(['.lake/build/bin/ux', str(out / 'restored-queued'), 'queued'], 'restored-queued')
assert result.returncode == 0, result.stdout
print('all 10 controls rejected; both restored UX suites pass', flush=True)
