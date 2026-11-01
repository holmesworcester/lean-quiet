#!/usr/bin/env python3
"""Two actual Lean runner processes. Retain all logs and databases on failure."""
import pathlib, re, socket, subprocess, sys, time
mode = sys.argv[1] if len(sys.argv) > 1 else 'lan'
out = pathlib.Path('out/endpoints') / (mode + '-' + str(time.time_ns()))
out.mkdir(parents=True)
# Reserve two presently unused TCP ports; the test processes bind immediately.
socks = [socket.socket() for _ in range(2)]
for s in socks: s.bind(('0.0.0.0', 0))
ports = [s.getsockname()[1] for s in socks]
for s in socks: s.close()
lan = subprocess.check_output(['ip', '-4', 'route', 'get', '224.0.0.251'], text=True).split(' src ')[1].split()[0]
host = lan if mode == 'lan' else '127.0.0.1'
barrier = out / 'go'
processes, logs = [], []
try:
    for i, name in enumerate(('A', 'B')):
        log = (out / (name + '.log')).open('w'); logs.append(log)
        args = ['.lake/build/bin/endpoint_network', name, str(out / (name + '.db')), str(ports[i]),
                mode, f'{host}:{ports[i]}', '55', f'{host}:{ports[1-i]}', str(barrier),
                '1000' if i == 1 and '--late' in sys.argv else '0',
                'late' if '--late' in sys.argv else '']
        p = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT); processes.append(p)
    if mode == 'simultaneous':
        time.sleep(1); barrier.touch()
    results = [p.wait(timeout=80) for p in processes]
    for log in logs: log.close()
    texts = [(out / (name + '.log')).read_text() for name in ('A', 'B')]
    for t in texts: print(t, end='')
    if any(results) or not all('PASS ' in t for t in texts):
        raise RuntimeError(f'network test failed: {results}')
    ids = [t.split('single stable session ')[1].split(';')[0] for t in texts]
    if ids[0] != ids[1]: raise RuntimeError(f'peers chose different sessions: {ids}')
    if mode == 'simultaneous':
        answers = [set(re.findall(r'ANSWER [AB] ([0-9a-f]+)', t)) for t in texts]
        if not all(len(a) == 1 for a in answers):
            raise RuntimeError(f'expected one independently answered attempt at each end: {answers}')
        if '--late' in sys.argv and next(iter(answers[0])) <= next(iter(answers[1])):
            raise RuntimeError('late attempt must lose to exercise retirement before selection')
        both = set.union(*answers)
        if len(both) != 2 or ids[0] != min(both):
            raise RuntimeError(f'expected minimum of two distinct authenticated attempts: {both}, kept {ids}')
    print(f'PASS {mode}: same authenticated session at both ends; logs: {out}')
finally:
    for p in processes:
        if p.poll() is None:
            p.terminate()
            try: p.wait(timeout=3)
            except subprocess.TimeoutExpired: p.kill(); p.wait()
    for log in logs: log.close()
    print(f'Artifacts retained: {out}')
