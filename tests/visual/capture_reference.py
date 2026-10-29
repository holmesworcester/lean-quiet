"""Explicitly refresh pinned libquiet reference frames, never during comparison CI."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import time
import urllib.error
import urllib.request

from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[2]
SPEC = json.loads((ROOT / 'tests/visual/reference.json').read_text())
FIXTURE = ROOT / 'tests/visual/Parity.stories.ts'


def provenance():
    return {**SPEC, 'fixture_sha256': hashlib.sha256(FIXTURE.read_bytes()).hexdigest()}


def capture(url, destination, chrome=None, cases=None):
    with urllib.request.urlopen(url + '/parity-provenance.json', timeout=10) as response:
        if json.load(response) != provenance():
            raise RuntimeError('reference server source/fixture provenance does not match')
    destination.mkdir(parents=True, exist_ok=True)
    with sync_playwright() as pw:
        options = {'headless': True}
        if chrome:
            options['executable_path'] = chrome
        browser = pw.chromium.launch(**options)
        try:
            for line in (cases or ROOT / 'tests/visual/cases.tsv').read_text().splitlines():
                if not line or line.startswith('#'):
                    continue
                fields = line.split('\t')
                name, width, height, theme, scenario = fields[:5]
                scenario, _, hover_name = scenario.partition('@')
                zoom = int(fields[5]) / 100 if len(fields) == 6 else 1
                import math
                # Browser zoom is a smaller CSS viewport at a larger device
                # scale, not a screenshot enlarged after layout. One edge may
                # be rounded by less than one device pixel; crop that edge.
                page = browser.new_page(viewport={'width': math.ceil(int(width)/zoom), 'height': math.ceil(int(height)/zoom)},
                                        device_scale_factor=SPEC['device_scale_factor'] * zoom,
                                        color_scheme=theme, locale=SPEC['locale'], timezone_id=SPEC['timezone'])
                try:
                    page.goto(f'{url}/iframe.html?id=parity-app--{scenario}&viewMode=story'
                              f'&globals=theme:{theme};face:bundled')
                    page.locator('.shell').wait_for(timeout=60_000)
                    page.evaluate('document.fonts.ready')
                    # The fixture intentionally selects System. App owns the
                    # theme attribute, so the Storybook toolbar alone cannot
                    # select dark mode: the simulated OS must agree.
                    panel = page.evaluate("getComputedStyle(document.documentElement).getPropertyValue('--panel').trim()")
                    expected_panel = '#222222' if theme == 'dark' else '#ffffff'
                    if panel.lower() != expected_panel:
                        raise RuntimeError(f'{name}: wrong actual theme {panel}, wanted {expected_panel}')
                    # Disable transient motion without hiding any content.
                    page.add_style_tag(content='*,*::before,*::after{animation:none!important;transition:none!important;caret-color:transparent!important}')
                    # Let query subscriptions and ResizeObserver measurements settle.
                    if scenario == 'conversation':
                        page.locator('.said').last.wait_for()
                    if scenario.startswith('switcher'):
                        popup = page.locator('[data-switcher="desktop"]')
                        popup.wait_for()
                        if scenario == 'switcher-end':
                            popup.evaluate('(el) => {el.scrollTop = el.scrollHeight}')
                        if scenario == 'switcher-hover':
                            popup.get_by_role('button', name='Community settings', exact=True).hover()
                    page.wait_for_timeout(250)
                    if hover_name:
                        spec = json.loads((ROOT / 'tests/visual/hover-targets.json').read_text())[hover_name]
                        target = page.locator(spec['selector'])
                        if 'text' in spec:
                            target = target.filter(has_text=spec['text'])
                        target = target.nth(spec.get('nth', 0))
                        target.wait_for(state='visible')
                        target.scroll_into_view_if_needed()
                        page.mouse.move(int(width)/zoom-1, 1)
                        page.wait_for_timeout(50)
                        (destination / 'rest').mkdir(exist_ok=True)
                        page.screenshot(path=str(destination / 'rest' / f'{name}.png'), animations='disabled')
                        box = target.bounding_box()
                        points = []
                        def point_at(el):
                            r = el.bounding_box()
                            x, y = r['x']+r['width']/2, r['y']+r['height']/2
                            page.mouse.move(x, y)
                            points.append((round(x*zoom), round(y*zoom)))
                        point_at(target)
                        if spec.get('action'):
                            point_at(target.locator(spec['action']))
                        page.wait_for_timeout(100)
                        region = [box['x'], box['y'], box['x']+box['width'], box['y']+box['height']]
                        if spec.get('message'):
                            bar = target.locator('.said-actions').bounding_box()
                            region = [min(region[0],bar['x']-20),min(region[1],bar['y']-20),max(region[2],bar['x']+bar['width']+20),max(region[3],bar['y']+bar['height']+20)]
                            if spec.get('action'):
                                tip = target.locator(spec['action']).locator('..').locator('.tip').bounding_box()
                                region = [min(region[0],tip['x']),min(region[1],tip['y']),max(region[2],tip['x']+tip['width']),max(region[3],tip['y']+tip['height'])]
                        region = [max(0,round(v*zoom)) for v in region]
                        region[2],region[3]=min(int(width),region[2]),min(int(height),region[3])
                        (destination / f'{name}.hover.json').write_text(json.dumps({'target':spec,'region':region,'pointer':points,'cursor':target.evaluate('(el)=>getComputedStyle(el).cursor')},indent=2)+'\n')
                        (destination / f'{name}.hover.tsv').write_text(''.join(f'{x}\t{y}\n' for x,y in points))
                    page.screenshot(path=str(destination / f'{name}.png'), animations='disabled')
                    if zoom != 1:
                        from PIL import Image
                        with Image.open(destination / f'{name}.png') as im:
                            im.crop((0, 0, int(width), int(height))).save(destination / f'{name}.png')
                    geometry = page.evaluate('''() => [...document.querySelectorAll('.pane-list,.pane-thread,.drawer,.drawer-body,.composer,.sidebar,.virtual-row,.said,.author,.text,[data-switcher=desktop],.panel-head,.panel-list,.sw-row,.sw-pick,.sw-tile,.sw-tool,.sw-label')].map(el => {
                      const r=el.getBoundingClientRect(); return {selector:el.className, x:r.x,y:r.y,w:r.width,h:r.height,scrollTop:el.scrollTop,scrollHeight:el.scrollHeight,clientHeight:el.clientHeight,scale:devicePixelRatio,display:getComputedStyle(el).display,font:getComputedStyle(el).font,padding:getComputedStyle(el).padding}
                    })''')
                    if not hover_name:
                        (destination / f'{name}.json').write_text(json.dumps(geometry, indent=2) + '\n')
                    print(f'reference: {name}', flush=True)
                finally:
                    page.close()
            (destination / 'provenance.json').write_text(json.dumps({**provenance(), 'browser_version': browser.version}, indent=2) + '\n')
        finally:
            browser.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=os.environ.get('LIBQUIET', '/home/holmes/libquiet'))
    parser.add_argument('--output', type=Path, default=ROOT / 'tests/visual/reference')
    parser.add_argument('--cases', type=Path, help='Optional zoom matrix: sixth column is browser zoom percent')
    parser.add_argument('--chrome', default=os.environ.get('CHROME'))
    parser.add_argument('--url', help='Use an already staged pinned reference server')
    args = parser.parse_args()
    if args.url:
        capture(args.url, args.output, args.chrome, args.cases)
        return
    work = ROOT / 'out/visual/reference-source' / SPEC['commit']
    work.mkdir(parents=True, exist_ok=True)
    # Export tracked source at the recorded commit; never edit the reference worktree.
    archive = subprocess.Popen(['git', '-C', str(args.source), 'archive', SPEC['commit'], 'app'], stdout=subprocess.PIPE)
    extracted = subprocess.run(['tar', '-x', '-C', str(work)], stdin=archive.stdout)
    archive.stdout.close()
    if archive.wait() or extracted.returncode:
        raise RuntimeError('could not export the pinned libquiet source')
    app = work / 'app'
    shutil.copyfile(FIXTURE, app / 'src/Parity.stories.ts')
    (app / 'public').mkdir(exist_ok=True)
    (app / 'public/parity-provenance.json').write_text(json.dumps(provenance()))
    subprocess.run(['pnpm', 'install', '--frozen-lockfile', '--store-dir', str(ROOT / 'out/visual/pnpm-store')], cwd=app, check=True)
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    url = f'http://127.0.0.1:{port}'
    env = {**os.environ, 'STORYBOOK_DISABLE_TELEMETRY': '1'}
    with (ROOT / 'out/visual/reference-server.log').open('w') as log:
        server = subprocess.Popen([str(app / 'node_modules/.bin/storybook'), 'dev', '--port', str(port),
                                   '--host', '127.0.0.1', '--no-open', '--ci'], cwd=app, stdout=log, stderr=log, env=env)
        try:
            deadline = time.monotonic() + 90
            while True:
                if server.poll() is not None:
                    raise RuntimeError('reference server failed; see out/visual/reference-server.log')
                try:
                    urllib.request.urlopen(url + '/index.json', timeout=2).close()
                    break
                except (urllib.error.URLError, TimeoutError):
                    if time.monotonic() > deadline:
                        raise RuntimeError('reference server timed out')
                    time.sleep(.2)
            capture(url, args.output, args.chrome, args.cases)
        finally:
            server.terminate()
            try:
                server.wait(timeout=10)
            except subprocess.TimeoutExpired:
                server.kill()
                server.wait()


if __name__ == '__main__':
    main()
