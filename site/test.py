#!/usr/bin/env python3
"""The join page in a real browser (headless Chromium, --dump-dom), from
the built site (site/build.py):

- a real invite (the app's own Community.Invite.text, from
  `.lake/build/bin/linkcheck --print`) shows the invite and links to
  leanquiet://join/ with exactly the fields after "#"; a device link
  (`--print-device`) on link.html links to leanquiet://link/;
- a link with anything but base62 after "#" (a quote, a tag, a scheme
  smuggled in), or too short, shows "broken" and links nowhere;
- no "#" shows the downloads only;
- the page's policy loads nothing: default-src 'none', no external
  script, style or image; the script runs only because its hash matches,
  which the negative control (a build with a wrong hash) shows: there the
  page never links the app;
- this device's row comes first (Android user agent: Android first);
- once the macOS / TestFlight URLs are given to the build, they are links.

Prerequisite: Chromium's headless shell (CHROME, or Playwright's in
~/.cache/ms-playwright). Artifacts: out/site-test/.
"""
import glob, html, os, re, subprocess, sys, tempfile
from pathlib import Path

root = Path(__file__).resolve().parent.parent
art = root / "out" / "site-test"
art.mkdir(parents=True, exist_ok=True)
chrome = os.environ.get("CHROME") or next(iter(sorted(glob.glob(
    os.path.expanduser("~/.cache/ms-playwright/chromium_headless_shell-*/chrome-*/chrome-headless-shell")))), None)
if not chrome:
    sys.exit("no headless Chromium: set CHROME")

fails = []
def ok(what, cond):
    print(("ok   " if cond else "FAIL ") + what)
    if not cond:
        fails.append(what)

def build(out, *extra):
    subprocess.run([sys.executable, str(root / "site/build.py"), str(out), *extra], check=True, capture_output=True)

def dom(site, frag, ua=None, name="page", page="join.html"):
    url = (site / page).as_uri() + frag
    with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR")) as prof:
        cmd = [chrome, "--headless", "--no-sandbox", "--disable-gpu", "--password-store=basic",
               f"--user-data-dir={prof}", "--virtual-time-budget=2000", "--dump-dom", url]
        if ua:
            cmd.insert(1, f"--user-agent={ua}")
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    (art / f"{name}.html").write_text(r.stdout)
    (art / f"{name}.log").write_text(r.stderr)
    return r.stdout

def shown(d, sid):
    m = re.search(rf'<section id="{sid}"( hidden="")?', d)
    return bool(m) and m.group(1) is None

def opens(d):
    m = re.search(r'<a id="open" class="button" href="([^"]*)"', d)
    return html.unescape(m.group(1)) if m else None

# A real invite from the app's own code.
r = subprocess.run([str(root / ".lake/build/bin/linkcheck"), "--print"], capture_output=True, text=True)
links = [l for l in r.stdout.splitlines() if l.startswith("https://")]
ok("linkcheck --print gives the app's invite links", len(links) == 2)
link = links[0] if links else "https://holmesworcester.github.io/lean-quiet/join#x"
uris = [l for l in r.stdout.splitlines() if l.startswith("leanquiet://")]
page, code = link.split("#", 1)
ok("the app links to the published page", page == "https://holmesworcester.github.io/lean-quiet/join")

site = root / "out" / "site"
build(site)
built = (site / "join.html").read_text()
csp = re.search(r'Content-Security-Policy" content="([^"]*)"', built).group(1)
ok("policy: default-src 'none', hashed script and style only",
   "default-src 'none'" in csp and "script-src 'sha256-" in csp and "unsafe" not in csp)
ok("no external script, style or image", not re.search(r'<(script|link|img|iframe)[^>]*(src|href)=', built))
ok("referrer: none", '<meta name="referrer" content="no-referrer">' in built)

d = dom(site, "#" + code, name="invite")
ok("an invite shows the invite", shown(d, "invite") and not shown(d, "broken") and not shown(d, "none"))
ok("Open links leanquiet://join/ and the fields after #", opens(d) == "leanquiet://join/" + code)
ok("that is the URI the app's Invite.uri gives", uris[:1] == [opens(d)])

# A device link (Community.webLink): its own page, opening leanquiet://link/.
r = subprocess.run([str(root / ".lake/build/bin/linkcheck"), "--print-device"], capture_output=True, text=True)
dlinks = [l for l in r.stdout.splitlines() if l.startswith("https://")]
duris = [l for l in r.stdout.splitlines() if l.startswith("leanquiet://")]
ok("linkcheck --print-device gives the app's device link", len(dlinks) == 1)
dlink = dlinks[0] if dlinks else "https://holmesworcester.github.io/lean-quiet/link#x"
dpage, dcode = dlink.split("#", 1)
ok("a device link links to the published link page", dpage == "https://holmesworcester.github.io/lean-quiet/link")
dbuilt = (site / "link.html").read_text()
dcsp = re.search(r'Content-Security-Policy" content="([^"]*)"', dbuilt).group(1)
ok("the link page's policy: default-src 'none', hashed script and style only",
   "default-src 'none'" in dcsp and "script-src 'sha256-" in dcsp and "unsafe" not in dcsp)
d = dom(site, "#" + dcode, name="device", page="link.html")
ok("a device link shows on the link page", shown(d, "invite") and not shown(d, "broken") and "device" in d)
ok("Open links leanquiet://link/ and the fields after #", opens(d) == "leanquiet://link/" + dcode)
ok("that is the URI the app's Invite.uri gives for it", duris[:1] == [opens(d)])

for name, frag in [("quote", "#" + code[:60] + '"onmouseover="x'), ("tag", "#" + code[:60] + "<script>x</script>"),
                   ("scheme", "#javascript:alert(1)//" + code[:60]), ("short", "#abc"),
                   ("encoded", "#" + code[:60] + "%22%3E")]:
    d = dom(site, frag, name=f"bad-{name}")
    ok(f"{name}: broken, links nowhere", shown(d, "broken") and not shown(d, "invite") and opens(d) == "#")

d = dom(site, "", name="none")
ok("no invite: downloads only", shown(d, "none") and not shown(d, "invite") and not shown(d, "broken"))
ok("Android and Linux (.deb, .tar.gz) download from the latest release",
   all(f"releases/latest/download/{n}" in d for n in
       ["lean-quiet-android.apk", "lean-quiet-linux-amd64.deb", "lean-quiet-linux-x86_64.tar.gz"]))

android = "Mozilla/5.0 (Linux; Android 15; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0 Mobile Safari/537.36"
d = dom(site, "#" + code, ua=android, name="android")
first = re.search(r'<ul id="downloads">\s*<li[^>]*data-os="(\w+)"', d)
ok("Android sees Android first", bool(first) and first.group(1) == "android")

later = root / "out" / "site-later"
build(later, "--mac-url", "https://example.org/LeanQuiet.zip", "--windows-url", "https://example.org/LeanQuiet-windows-x64.zip",
      "--testflight-url", "https://testflight.apple.com/join/abcd1234")
d = dom(later, "", name="later")
ok("given URLs become links", 'href="https://example.org/LeanQuiet.zip"' in d and 'href="https://example.org/LeanQuiet-windows-x64.zip"' in d
   and 'href="https://testflight.apple.com/join/abcd1234">TestFlight' in d)

# Negative control: with a wrong script hash the policy blocks the script,
# and the page must not link the app. The checks above would fail.
bad = root / "out" / "site-bad"
build(bad, "--bad-hash")
d = dom(bad, "#" + code, name="negative")
ok("negative control: a wrong hash blocks the script", opens(d) == "#" and not shown(d, "invite"))

print(f"site: {len(fails)} failed" if fails else "site: all passed")
sys.exit(1 if fails else 0)
