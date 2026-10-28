#!/usr/bin/env python3
"""Sends control commands to the app in the Simulator (ctl_ios.c: TCP on
the Mac's 127.0.0.1) and prints each reply. Runs on the Mac; from here,
pipe it through ssh:

    ssh MAC python3 - [-H HOST] [-p PORT] 'chaos 500' wait state < ios/ctl.py

HOST is 127.0.0.1 for the Simulator; a phone's address on the Mac's Wi-Fi
for the app on an iPhone launched with LEANQUIET_CTL_REMOTE=1. TOKEN (-T,
or LEANQUIET_CTL_TOKEN) is the channel's: the one the app was launched
with, sent first on every connection.

The commands are App.command's (ping, state, stats, chaos N, wait, send
TEXT, react I EMOJI, tray I, untray, browse, sheet ..., pause, resume,
bottom, scroll B, top, visible). Retries the connection for up to -w
seconds, so it can follow a launch.
"""
import argparse, os, socket, time

ap = argparse.ArgumentParser()
ap.add_argument("-H", "--host", default="127.0.0.1")
ap.add_argument("-T", "--token", default=os.environ.get("LEANQUIET_CTL_TOKEN", ""),
                help="the channel's token (sent first; without it the app answers nothing)")
ap.add_argument("-p", "--port", type=int, default=7417)
ap.add_argument("-t", "--timeout", type=float, default=600)
ap.add_argument("-w", "--wait", type=float, default=30)
ap.add_argument("cmds", nargs="+")
a = ap.parse_args()
deadline = time.time() + a.wait
while True:
    try:
        s = socket.create_connection((a.host, a.port), timeout=a.timeout)
        break
    except OSError:
        if time.time() > deadline:
            raise
        time.sleep(0.5)
f = s.makefile("rwb")
f.write((f"token {a.token}\n").encode()); f.flush()
if f.readline().decode().strip() != "ok":
    raise SystemExit("the app refused the token (or this is a build without the channel)")
for c in a.cmds:
    f.write((c + "\n").encode()); f.flush()
    line = f.readline()
    if not line:
        raise SystemExit(f"no reply to {c!r}: the app closed the connection")
    print(line.decode().rstrip("\n"), flush=True)
