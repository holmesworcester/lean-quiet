import os
import pathlib
import subprocess

out = pathlib.Path('out/seam')
out.mkdir(parents=True, exist_ok=True)
binary = pathlib.Path('.lake/build/bin/seam').resolve()

def raw(phase, pointer, x, y, time):
    return f'!raw {phase} {pointer} {x} {y} {time}'

script = ['!frames 2', '!ime 900', '!frames 2', f'!dump {out}/screen.ppm']
script += ['!begin', raw(0, 7, 100, 500, 1000), raw(2, 7, 100, 500, 1100), '!end']
script += ['!begin', raw(0, 7, 100, 500, 2000), raw(1, 7, 110, 510, 2100), raw(2, 7, 105, 505, 2200), '!end']
script += ['!begin', raw(0, 7, 100, 500, 3000), raw(1, 7, 140, 500, 3050), raw(2, 7, 100, 500, 3100), '!end']
script += ['!begin', raw(0, 7, 100, 500, 4000), raw(2, 7, 100, 500, 4500), '!end']
script += ['!begin', raw(0, 7, 100, 500, 5000), raw(0, 8, 300, 700, 5010), raw(1, 8, 600, 900, 5020), raw(2, 7, 100, 500, 5100), raw(2, 8, 300, 700, 5150), '!end']
script += ['!begin', raw(0, 7, 100, 500, 6000), raw(3, 7, 100, 500, 6100), '!end']
script += ['!begin', raw(0, 7, 100, 500, 7000)]
script += [raw(1, 7, 300 if i == 4500 else 100, 500, 7001+i) for i in range(5000)]
script += [raw(2, 7, 100, 500, 12100), '!end']
script += [raw(0, 7, 100, 500, 14000), '!frames 40', raw(2, 7, 100, 500, 14700)]
script += ['!key 66 0', '!key 66 1', '!key 65 0', '!key 40 0',
           '!usb-key 40 0', '!usb-key 40 1', '!usb-key 66 0', '!action 4', '!action 3']
script += ['!scroll -900', '!frames 2', '!scroll 999999', '!frames 2']
path = out / 'raw.script'
path.write_text('\n'.join(script) + '\n')
counts = 0
for mode in ['chat', 'page']:
    result = subprocess.run([str(binary), mode], env={**os.environ, 'QUIET_SCRIPT': str(path)},
                            capture_output=True, text=True, check=True)
    (out / f'{mode}.log').write_text(result.stdout + result.stderr)
    lines = result.stdout.splitlines()
    taps = [line for line in lines if line.startswith('tap ')]
    longs = [line for line in lines if line.startswith('long ')]
    distance = 1716 if mode == 'page' else 879
    assert taps == [f'tap App.Region.list 100 {distance}'] * 3, taps
    assert longs == [f'long App.Region.list 100 {distance}'] * 2, longs
    assert lines.count('send') == 3
    frames = [int(line.split()[1]) for line in lines if line.startswith('frame ')]
    assert min(frames) == 0 and max(frames) == 8748, frames
    data = (out / 'screen.ppm').read_bytes().split(b'\n', 3)[3]
    # Independent pixel oracle: a page starts at the header; a chat rides
    # up by the keyboard's excess over the navigation inset.
    for y in range(2400):
        value = 60000 if y < 128 else 60001 if y >= 1380 else y - 128 + 32 + (837 if mode == 'chat' else 0)
        expected = bytes((value % 256, value // 256, 77))
        assert data[y*1080*3:(y+1)*1080*3] == expected * 1080, (mode, y)
    counts += 1
samples = sum(line.startswith('!raw ') for line in script) * counts
print(f'seam: {counts} C-twin sessions, {samples} raw touch samples, 4,800 pixel rows; all passed')
