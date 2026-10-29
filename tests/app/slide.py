"""Check the actual generated export bodies, including compiler primitives.
Lean emits lean_uint*_add/sub/etc for C inline integer operators. Their
exact header bodies are audited here; no other call, object, or once-cell
is allowed. Optimized assembly must contain no call or Lean symbol at all.
"""
import pathlib
import re
import subprocess

root = pathlib.Path(__file__).resolve().parents[2]
out = root / 'out/thread'
out.mkdir(parents=True, exist_ok=True)
exports = ['lq_slide_edge', 'lq_slide_delta', 'lq_slide_source', 'lq_slide_fill_row']
# Exact leaf implementations from the pinned toolchain's lean.h.
primitives = {
    'lean_uint32_dec_lt': 'return a1 < a2;',
    'lean_uint32_to_uint64': 'return ((uint64_t)a);',
    'lean_uint64_add': 'return a1+a2;',
    'lean_uint64_sub': 'return a1-a2;',
    'lean_uint64_dec_lt': 'return a1 < a2;',
    'lean_uint64_dec_le': 'return a1 <= a2;',
    'lean_uint64_mod': 'return a2 == 0 ? a1 : a1%a2;',
    'lean_uint64_to_uint32': 'return ((uint32_t)a);',
    'lean_uint8_dec_eq': 'return a1 == a2;',
    'lean_uint32_sub': 'return a1-a2;',
}
def body(source, name):
    found = list(re.finditer(r'\b' + re.escape(name) + r'\([^;{}]*\)\s*\{', source))
    assert len(found) == 1, (name, 'missing or duplicate body', len(found))
    start = pos = found[0].end()
    depth = 1
    while depth:
        depth += (source[pos] == '{') - (source[pos] == '}')
        pos += 1
    return source[start:pos-1]
def compact(s): return re.sub(r'\s+', '', s)
prefix = pathlib.Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
header = (prefix/'include/lean/lean.h').read_text()
source = root/'.lake/build/ir/engine/renderer/Slide.c'
code = source.read_text()
for name in exports:
    text = body(code, name)
    calls = set(re.findall(r'\b((?:lean_|lp_|lq_|_init_)\w+)\s*\(', text))
    assert calls <= primitives.keys(), (name, 'non-scalar calls', sorted(calls-primitives.keys()))
    assert not re.search(r'lean_object|once|_closed__', text), (name, 'object or once-cell')
    for call in calls:
        assert compact(body(header, call)) == compact(primitives[call]), (call, 'primitive changed')
    (out/f'{name}.c.txt').write_text(text)
asm = out/'Slide.s'
subprocess.run(['cc', '-O2', '-S', '-I'+str(prefix/'include'), str(source), '-o', str(asm)], check=True)
assembly = asm.read_text()
for name in exports:
    text = assembly.split(name+':\n', 1)[1].split('.size\t'+name, 1)[0]
    assert not re.search(r'\b(call\w*|lean_\w+|lp_\w+)\b', text), (name, 'non-leaf assembly')
print('slide C: 4 exports, 10 audited scalar primitives, no object/once-cell/app calls; assembly has zero calls')
# Link just the exports, without libInit or any Lean runtime library.
obj = out/'Slide.o'
subprocess.run(['cc', '-O2', '-ffunction-sections', '-fdata-sections', '-I'+str(prefix/'include'),
                '-c', str(source), '-o', str(obj)], check=True)
subprocess.run(['cc', '-O2', '-std=gnu11', '-pthread', '-Wl,--gc-sections', str(root/'tests/app/slide.c'),
                str(obj), '-o', str(out/'slide')], check=True)
subprocess.run([str(out/'slide')], check=True)

# Entry-point order matters as well as the TLS helper itself.
for path, name, before, after in [
    ('platforms/android/twin/layer.c', 'bl_run', 'lq_slide_thread_init()', 'ALooper_prepare'),
    ('platforms/android/twin/layer.c', 'bl_start', 'lq_slide_warm()', 'pthread_create'),
    ('platforms/ios/quiet_ios.m', 'lq_translate', 'lq_slide_thread_init()', 'lq_slide_rect'),
    ('platforms/ios/quiet_ios.m', 'lq_frame', 'lq_slide_warm()', 'dispatch_sync'),
    ('platforms/headless/host.c', 'lq_screen', 'lq_slide_thread_init()', 'lq_slide_warm()'),
    ('platforms/headless/host.c', 'lq_frame', 'lq_slide_thread_init()', 'lq_slide_warm()'),
]:
    text = body((root/path).read_text(), name)
    assert before in text and after in text and text.index(before) < text.index(after), (path, name, 'thread/warm order')
print('slide entry points: 6 initialization/warm-up order checks passed')
