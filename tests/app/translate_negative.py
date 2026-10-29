"""Break the running translation/fill, require a proof or twin failure.
Sources and compiled artifacts are restored before returning.
"""
import pathlib
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[2]
logs = root / 'out/translate/negative'
logs.mkdir(parents=True, exist_ok=True)
def run(args, name):
    r = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=180)
    (logs / f'{name}.log').write_text(r.stdout+r.stderr)
    return r.returncode
assert run(['lake', 'build', 'translate', 'engine.renderer.TranslateLaws'], 'baseline') == 0
cases = [
    ('direction', 'engine/renderer/Translate.lean', 'origin + if pin', 'origin - if pin', 'law'),
    ('pinned-scroll', 'engine/renderer/Translate.lean', 'origin + if pin', 'origin + if false', 'law'),
    ('extent-edge', 'engine/renderer/Translate.lean', '0 ≤ r ∧ r < height', '0 ≤ r ∧ r + 1 < height', 'law'),
    ('crop-slide', 'engine/renderer/Translate.lean', 'Surface.crop (position pin base origin sample)', 'Surface.crop (position pin base origin sample + 1)', 'law'),
    ('fill-gap', 'engine/renderer/Translate.lean', '(top : Int) - 48 +', '(top : Int) + 48 +', 'law'),
    ('tile-frozen', 'engine/renderer/Translate.lean', 'if pin then base else sample', 'if pin then base else base', 'law'),
    ('outside-blank', 'engine/renderer/Translate.lean', '| none => .unloaded', '| none => .blank', 'law'),
    ('unpainted-line', 'engine/renderer/Translate.lean', '| none => .unloaded', '| none => .line 0 0', 'law'),
    ('wire-edge', 'engine/renderer/Translate.lean', 'else r.dst1).toUInt32', 'else r.dst1).toUInt32 + 1', 'law'),
    ('fill-index', 'engine/renderer/Translate.lean', 'bottom.toNat).toNat.toUInt32', 'bottom.toNat).toNat.toUInt32 + 1', 'law'),
    ('wire-source', 'engine/renderer/Translate.lean', '(r : Int).toInt64', '(r + 1 : Int).toInt64', 'law'),
    ('wire-delta', 'engine/renderer/Translate.lean', 'else sample.toInt - base.toNat).toInt32', 'else sample.toInt - base.toNat + 1).toInt32', 'law'),
    ('tile-pixels', 'engine/renderer/Hold.lean', 'holdLine s (47 - i)', 'holdLine s (48 - i)', 'law'),
    ('tap-shift', 'engine/renderer/Input.lean', '(f.b : Int) + f.slide +', '(f.b : Int) +', 'law'),
    ('native-no-fill', 'platforms/headless/host.c', 'if (r < rows_of(hs.hold))', 'if (false && r < rows_of(hs.hold))', 'twin'),
    ('native-fill-order', 'platforms/android/twin/layer.c', 'k == BL_HOLD ? 0 : k + 1', 'k == BL_HOLD ? -1 : k', 'native'),
    ('native-fill-layer', 'platforms/android/twin/layer.c', 'if (bl_l[BL_HOLD].shown >= 0)', 'if (false && bl_l[BL_HOLD].shown >= 0)', 'native'),
    ('native-freeze', 'platforms/android/twin/layer.c', '(bl_ready || bl_published)', '(bl_ready)', 'native'),
]
if sys.argv[1:]:
    names = set(sys.argv[1:])
    assert names <= {c[0] for c in cases}
    cases = [c for c in cases if c[0] in names]
for name, rel, old, new, kind in cases:
    path = root/rel
    saved = path.read_text()
    assert saved.count(old) == 1, (name, saved.count(old))
    try:
        path.write_text(saved.replace(old, new))
        if kind == 'law':
            module = rel[:-5].replace('/', '.')
            assert run(['lake', 'build', module], name+'-build') == 0
            result = run(['lake', 'env', 'lean', 'engine/renderer/TranslateLaws.lean'], name)
        elif kind == 'twin':
            assert run(['lake', 'build', 'translate'], name+'-build') == 0
            result = run(['python3', 'tests/app/translate.py'], name)
        else:
            result = run(['bash', 'tests/app/layer.sh'], name)
        assert result != 0, (name, 'survived')
        print('detected', name, flush=True)
    finally:
        path.write_text(saved)
        assert run(['lake', 'build', 'engine.renderer.TranslateLaws'], name+'-restore') == 0
assert run(['lake', 'build', 'translate'], 'restored-build') == 0
assert run(['python3', 'tests/app/translate.py'], 'restored-twin') == 0
assert run(['bash', 'tests/app/layer.sh'], 'restored-native') == 0
print(f'translate negative controls: {len(cases)} detected; sources restored; suites pass')
