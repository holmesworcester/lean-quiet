"""Mutate the running exports and native guards; require failure and restore."""
import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parents[2]
logs = root/'out/thread/negative'
logs.mkdir(parents=True, exist_ok=True)
def run(args, name):
    p = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=180)
    (logs/(name+'.log')).write_text(p.stdout+p.stderr)
    return p.returncode
assert run(['bash', 'tests/app/slide.sh'], 'baseline') == 0
cases = [
    ('edge', 'engine/renderer/Slide.lean', 'crop which p h top.toUInt64 bottom.toUInt64', 'crop which p h top.toUInt64 bottom.toUInt64 + 1', 'law'),
    ('delta', 'engine/renderer/Slide.lean', 'else sample.toUInt32 - base', 'else sample.toUInt32 - base + 1', 'law'),
    ('pick', 'engine/renderer/Slide.lean', 'else 18446744073709551615', 'else 0', 'law'),
    ('fill', 'engine/renderer/Slide.lean', 'sub32 (12884901888 + y.toUInt64) (fillOrigin pin base top bottom sample)', 'sub32 (12884901888 + y.toUInt64) (fillOrigin pin base top bottom sample) + 1', 'law'),
    ('boxed', 'engine/renderer/Slide.lean', '(if pin then (0 : UInt32) else sample.toUInt32 - base).toInt32', '(if pin then (0 : Int) else sample.toInt - base.toNat).toInt32', 'native'),
    ('once', 'engine/renderer/Slide.lean', 'if a < b then 0 else (a - b).toUInt32', '(sub a b).toUInt32', 'native'),
    ('init-omit', 'platforms/native/thread.h', '    lean_initialize_thread();', '    /* initialization omitted */', 'native'),
    ('init-repeat', 'platforms/native/thread.h', 'if (!ready)', 'if (true)', 'native'),
    ('warm-omit', 'platforms/native/thread.h', '    sink = lq_slide_source(pin, 0, 0, 1, 0, 0);', '    /* source warm-up omitted */', 'native'),
    ('android-entry', 'platforms/android/twin/layer.c', '  lq_slide_thread_init();', '  /* entry omitted */', 'native'),
    ('ios-entry', 'platforms/ios/quiet_ios.m', '  lq_slide_thread_init();', '  /* entry omitted */', 'native'),
    ('host-entry', 'platforms/headless/host.c', '  lq_slide_thread_init();\n  lq_slide_warm();\n  (void)pin;', '  lq_slide_warm();\n  (void)pin;', 'native'),
]
for name, rel, before, after, kind in cases:
    path = root/rel
    original = path.read_text()
    assert original.count(before) == 1, (name, original.count(before))
    try:
        path.write_text(original.replace(before, after))
        assert run(['lake', 'build', '+engine.renderer.Slide:c'], name+'-build') == 0
        cmd = ['lake', 'env', 'lean', 'engine/renderer/SlideLaws.lean'] if kind == 'law' else ['python3', 'tests/app/slide.py']
        assert run(cmd, name) != 0, (name, 'survived')
        print('detected', name, flush=True)
    finally:
        path.write_text(original)
        assert run(['lake', 'build', 'engine.renderer.SlideLaws', '+engine.renderer.Slide:c'], name+'-restore') == 0
assert run(['bash', 'tests/app/slide.sh'], 'restored') == 0
print(f'slide negative controls: {len(cases)} detected; sources restored; suite passes')
