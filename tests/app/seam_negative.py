"""Deliberately break running functions, require detection, restore them.
Run only in an idle worktree; every mutation is restored in a finally block.
"""
import os
import pathlib
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[2]
logs = root / 'out/seam/negative'
logs.mkdir(parents=True, exist_ok=True)

def run(args, name):
    result = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=120)
    (logs / f'{name}.log').write_text(result.stdout + result.stderr)
    return result.returncode

cases = [
    ('redundant-geometry', 'platforms/android/twin/layer.c', 'if (!bl_ready && sample == bl_applied_sample) goto complete_tick;', '/* broken: every idle vsync takes the callback slot */', 'native'),
    ('trace-wrong-position', 'platforms/android/twin/layer.c', 'done->composer_y = bl_place[10];',
     'done->composer_y = bl_place[15];', 'native'),
    ('trace-even-disabled', 'platforms/android/twin/layer.c', 'if (bl_trace && d->composer_visible)', 'if (d->composer_visible)', 'native'),
    ('trace-submitted', 'platforms/android/twin/layer.c', 'ASurfaceTransaction_setOnComplete(t, done, bl_complete);',
     '__android_log_print(ANDROID_LOG_INFO, "leantrace", "submitted composer-y %u", done->composer_y);\n    ASurfaceTransaction_setOnComplete(t, done, bl_complete);', 'native'),
    ('revoked-release', 'engine/renderer/Input.lean', 'press := none, frames := []', 'press := s.press, frames := []', 'input'),
    ('unmount-input', 'app/Screen.lean', 'life := s.life.unmount, input := Input.revoke s.input,', 'life := s.life.unmount,', 'app'),
    ('resize-input', 'app/Screen.lean', 'dim := dm, input := Input.revoke s.input,', 'dim := dm,', 'app'),
    ('page-slide', 'engine/renderer/Surface.lean', 'if pin then Seam.pinned', 'if false then Seam.pinned', 'surface'),
    ('conversation-offset', 'engine/renderer/Surface.lean', 'else Seam.place g over bf bn 0', 'else Seam.place g over bf (bn + 1) 0', 'surface'),
    ('crop-shift', 'engine/renderer/Surface.lean', 'origin, crop origin height', 'origin, crop (origin + 1) height', 'surface'),
    ('composer-covered', 'engine/renderer/Surface.lean', 'g.composerTop, g.h⟩', 'g.composerTop + 1, g.h⟩', 'surface'),
    ('wire-shift', 'engine/renderer/Surface.lean', 'r.dst0.toUInt32, r.dst1', '(r.dst0 + 1).toUInt32, r.dst1', 'surface'),
    ('unbounded-offset', 'engine/renderer/Surface.lean', 'min sample.toNat maxB', 'max sample.toNat maxB', 'surface'),
    ('forget-excursion', 'engine/renderer/Input.lean', 'max p.travel (distance p.first.pos t.pos)', 'distance p.first.pos t.pos', 'input'),
    ('slop-boundary', 'engine/renderer/Input.lean', 'p.travel > p.context.slop ∨', 'p.travel ≥ p.context.slop ∨', 'input'),
    ('early-long', 'engine/renderer/Input.lean', 'time - p.first.time < 500', 'time - p.first.time < 499', 'input'),
    ('move-down-position', 'engine/renderer/Input.lean', 'some (.tap p.first.pos)', 'some (.tap ⟨p.first.pos.x + 1, p.first.pos.y⟩)', 'input'),
    ('second-pointer', 'engine/renderer/Input.lean', 'if t.id != p.first.id then', 'if false then', 'input'),
    ('replace-owner', 'engine/renderer/Input.lean', 'if s.pointers.isEmpty then', 'if true then', 'input'),
    ('page-tap-lift', 'engine/renderer/Input.lean', '(f.g.composerTop : Int) + f.g.shift - 1 - y', '(f.g.composerTop : Int) - 1 - y', 'input'),
    ('content-tap-shift', 'engine/renderer/Input.lean', 'else (f.b : Int) + f.slide + f.g.composerTop - 1 - y', 'else (f.b : Int) + f.slide + f.g.composerTop - y', 'input'),
    ('delivered-key-shift', 'engine/renderer/Input.lean', '.tap (region f p) p.x.toNat.toUInt32', '.tap (region f p) (p.x.toNat + 1).toUInt32', 'input'),
    ('wrong-ime-action', 'engine/renderer/Input.lean', 'if action == 4 then [.send]', 'if action == 3 then [.send]', 'unit'),
    ('cancel-as-up', 'engine/renderer/Input.lean', '[.drag t.phase.toUInt32', '[.drag (min t.phase 2).toUInt32', 'unit'),
    ('ignore-sheet-cancel', 'app/Screen.lean', 'if ph == 3 then', 'if false then', 'app'),
    ('native-drop-move', 'platforms/headless/host.c', '  if (hs.n + 8 > hs.cap)', '  if (k == 10 && hs.n >= 32768) return;\n  if (hs.n + 8 > hs.cap)', 'twin'),
    ('wrong-frame', 'engine/renderer/Session.lean', 'frames := pending', 'frames := []', 'unit'),
    ('accept-rejected-frame', 'engine/renderer/Session.lean', 'let published := accepted raw', 'let published := true', 'unit'),
    ('prune-before-drain', 'engine/renderer/Session.lean', '(serial, context) :: state.frames else state.frames', '(serial, context) :: state.frames.take 2 else state.frames', 'unit'),
    ('forget-on-rejection', 'engine/renderer/Session.lean', 'else state.frames\n  return', 'else []\n  return', 'unit'),
    ('wait-completion', 'platforms/android/twin/layer.c', '!bl_ready && !bl_awaiting_completion &&', '!bl_ready &&', 'native'),
    ('old-window-completion', 'platforms/android/twin/layer.c', 'if (finished && d->generation == bl_generation)', 'if (true)', 'native'),
    ('completion-wraps-generation', 'platforms/android/twin/layer.c', 'if (finished && d->generation == bl_generation)', 'if (d->generation == bl_generation)', 'native'),
    ('unbounded-completions', 'platforms/android/twin/layer.c', '&& !bl_completion.pending &&', '&&', 'native'),
    ('completion-ignores-reset', 'platforms/native/frame_completion.h', 'if (s->revoked || ticket.generation != s->generation)', 'if (false)', 'native'),
    ('completion-wraps-identity', 'platforms/native/frame_completion.h', 'if (s->accepted == UINT64_MAX) return false;', '', 'native'),
    ('mixed-publication', 'platforms/android/twin/layer.c', 'bool ok = !bl_ready &&', 'bool ok =', 'native'),
    ('failed-buffer', 'platforms/android/twin/layer.c', 'return submitted;', 'return true;', 'native'),
    ('key-code-collision', 'engine/renderer/Input.lean', 'code == enter &&', '(code == 66 || code == 40) &&', 'unit'),
    ('early-frame-stamp', 'platforms/android/twin/layer.c', 'ASurfaceTransaction_setOnComplete(t, done, bl_complete);',
     'atomic_store(&bl_view, done->view);\n    ASurfaceTransaction_setOnComplete(t, done, bl_complete);', 'native'),
]
# Runtime controls must compile and fail their intended assertion; a compiler
# error, timeout or signal is not evidence that the behavior was detected.
native_failures = {'redundant-geometry': 'unchanged geometry leaves the native callback slot available', 'trace-wrong-position': 'trace captures the actual completed composer destination', 'trace-even-disabled': 'debug-disabled composition emits no per-frame trace', 'trace-submitted': 'staging and submission do not emit a presentation trace', 'wait-completion': 'consumed geometry waits for its own completion', 'old-window-completion': 'replacement presentation recovers after its own completion', 'completion-wraps-generation': 'replacement presentation recovers after its own completion', 'unbounded-completions': 'pending animation callback holds new geometry without allocating another callback', 'completion-ignores-reset': 'reset retires delayed ownership without accepting old-surface completion', 'completion-wraps-identity': 'exhausted native identity counters fail closed instead of aliasing a candidate', 'mixed-publication': "pending publication blocks next frame's different dirty layer", 'failed-buffer': 'buffer lock failure propagates', 'early-frame-stamp': 'submitted frame is not stamped until presentation completes'}
# --list: the cases, one a line; names given: just those (ci/local.sh
# --full runs them in slices, each in its own copy of the tree).
if sys.argv[1:] == ['--list']:
    print('\n'.join(case[0] for case in cases))
    sys.exit(0)
if sys.argv[1:]:
    selected = set(sys.argv[1:])
    assert selected <= {case[0] for case in cases}, 'unknown mutation'
    cases = [case for case in cases if case[0] in selected]
assert run(['lake', 'build', 'engine.renderer.InputLaws', 'seam', 'seam_app'], 'baseline') == 0
for name, relative, old, new, kind in cases:
    path = root / relative
    saved = path.read_text()
    assert old in saved, (name, 'mutation anchor missing')
    try:
        path.write_text(saved.replace(old, new, 1))
        if kind == 'surface':
            result = run(['lake', 'env', 'lean', relative], name)
        elif kind == 'input':
            assert run(['lake', 'build', 'engine.renderer.Input'], name + '-build') == 0
            result = run(['lake', 'env', 'lean', 'engine/renderer/InputLaws.lean'], name)
        elif kind == 'native':
            assert run(['bash', 'tests/app/layer.sh', '--build-only'], name + '-build') == 0, (name, 'native mutant must compile')
            result = run(['out/seam/layer'], name)
            expected = 'FAIL layer: ' + native_failures[name]
            assert result == 1 and expected in (logs / f'{name}.log').read_text(), (name, 'wrong native failure')
        else:
            target = 'seam_app' if kind == 'app' else 'seam'
            assert run(['lake', 'build', target], name + '-build') == 0
            command = ['.lake/build/bin/seam_app'] if kind == 'app' else (
                ['.lake/build/bin/seam', 'unit'] if kind == 'unit' else ['python3', 'tests/app/seam.py'])
            result = run(command, name)
        assert result != 0, (name, 'negative control survived')
        print('detected', name, flush=True)
    finally:
        path.write_text(saved)
        # Restore artifacts too, before testing the next independent mutation.
        assert run(['lake', 'build', 'engine.renderer.InputLaws'] + (['seam_app'] if kind == 'app' else []),
                   name + '-restore') == 0
if os.environ.get('CI_LANE') == '1':
    # a copy of the tree thrown away after: its suites ran in their own part
    print(f'negative controls: {len(cases)} detected')
    sys.exit(0)
assert run(['lake', 'build', 'seam', 'seam_app'], 'restored') == 0
assert run(['python3', 'tests/app/seam.py'], 'restored-twin') == 0
assert run(['.lake/build/bin/seam_app'], 'restored-app') == 0
assert run(['bash', 'tests/app/layer.sh'], 'restored-native') == 0
print(f'negative controls: {len(cases)} detected; restored suites pass')
