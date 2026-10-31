#!/usr/bin/env python3
"""Builds the join page site into OUT (default out/site).

usage: site/build.py [OUT] [--mac-url URL] [--testflight-url URL] [--bad-hash]

- join.html: site/join.html with its Content-Security-Policy hashes filled
  in (the one inline script and style are the only code the page may run),
  and the macOS and TestFlight links, when given, in their data-url slots;
- index.html: sends visitors to join (no invite there: the downloads);
- .nojekyll: GitHub Pages serves the files as they are.

--bad-hash writes a wrong script hash: the negative control for site/test.py.
"""
import base64, hashlib, re, sys
from pathlib import Path

here = Path(__file__).resolve().parent
args = sys.argv[1:]

def opt(name):
    if name in args:
        i = args.index(name)
        v = args[i + 1]
        del args[i:i + 2]
        return v
    return ""

mac, testflight = opt("--mac-url"), opt("--testflight-url")
bad = "--bad-hash" in args
if bad:
    args.remove("--bad-hash")
out = Path(args[0] if args else here.parent / "out" / "site")
for url in (mac, testflight):
    if url and not re.fullmatch(r"https://[^\s\"'<>]+", url):
        sys.exit(f"not an https URL: {url}")

page = (here / "join.html").read_text()
if mac:
    page = page.replace('<li data-os="mac"><span>macOS (Apple silicon)</span><span class="soon" data-url="">',
                        f'<li data-os="mac"><span>macOS (Apple silicon)</span><span class="soon" data-url="{mac}">')
if testflight:
    page = page.replace('<li data-os="ios"><span>iPhone</span><span class="soon" data-url="">',
                        f'<li data-os="ios"><span>iPhone</span><span class="soon" data-url="{testflight}">')

def digest(tag):
    blocks = re.findall(rf"<{tag}>(.*?)</{tag}>", page, re.S)
    assert len(blocks) == 1, f"exactly one inline <{tag}>"
    return base64.b64encode(hashlib.sha256(blocks[0].encode()).digest()).decode()

script, style = digest("script"), digest("style")
if bad:
    script = base64.b64encode(hashlib.sha256(b"not the script").digest()).decode()
page = page.replace("@SCRIPT_HASH@", script).replace("@STYLE_HASH@", style)
assert "@" not in re.search(r'Content-Security-Policy" content="([^"]*)"', page).group(1)

out.mkdir(parents=True, exist_ok=True)
(out / "join.html").write_text(page)
(out / "index.html").write_text(
    '<!doctype html><meta charset="utf-8"><meta name="referrer" content="no-referrer">'
    '<meta http-equiv="refresh" content="0; url=join"><title>Lean Quiet</title>'
    '<a href="join">Lean Quiet downloads</a>\n')
(out / ".nojekyll").write_text("")
print(out)
