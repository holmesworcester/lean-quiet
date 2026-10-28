#!/usr/bin/env python3
"""Sends control commands to the app (abstract socket @leanquiet, through
adb forward) and prints each reply.

    tools/ctl.py [-s SERIAL] [-p PORT] 'chaos 500' wait state
"""
import argparse, socket, subprocess, os

ap = argparse.ArgumentParser()
ap.add_argument("-s", "--serial", default=os.environ.get("SERIAL", "emulator-5644"))
ap.add_argument("-p", "--port", type=int, default=7071)
ap.add_argument("-t", "--timeout", type=float, default=600)
ap.add_argument("cmds", nargs="+")
a = ap.parse_args()
adb = os.path.expanduser("~/android-sdk/platform-tools/adb")
subprocess.run([adb, "-s", a.serial, "forward", f"tcp:{a.port}", "localabstract:leanquiet"], check=True,
               stdout=subprocess.DEVNULL)
s = socket.create_connection(("127.0.0.1", a.port), timeout=a.timeout)
f = s.makefile("rwb")
for c in a.cmds:
    f.write((c + "\n").encode()); f.flush()
    print(f.readline().decode().rstrip("\n"), flush=True)
