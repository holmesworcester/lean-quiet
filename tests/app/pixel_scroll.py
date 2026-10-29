#!/usr/bin/env python3
"""Provisioned-device scroll measurement; preserves the installed app's data.

Requires SERIAL and an existing chat with messages. The Mise task builds
the APK; APK/OUT can select a baseline for a paired manual comparison.
No database reset, generated messages, or sent composer text.
"""
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
SERIAL = os.environ["SERIAL"]
OUT = Path(os.environ.get("OUT", str(ROOT / "out/pixel-scroll"))).resolve()
APK = Path(os.environ.get("APK", str(ROOT / "out/quiet-phone.apk"))).resolve()
ADB = [os.environ.get("ADB", str(Path.home() / "android-sdk/platform-tools/adb")), "-s", SERIAL]
OUT.mkdir(parents=True, exist_ok=True)
for name in ["scroll.mp4", "stopped.png"]:
    (OUT / name).unlink(missing_ok=True)
PKG = "com.holmes.leanquiet"
PORT = 35797
result = {"serial": SERIAL, "apk_sha256": hashlib.sha256(APK.read_bytes()).hexdigest(),
          "started": time.time(), "passed": False}


def adb(*args, timeout=60):
    p = subprocess.run(ADB + list(args), stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout, check=True)
    return p.stdout.decode().strip()


def ctl(command):
    with socket.create_connection(("127.0.0.1", PORT), timeout=8) as s:
        s.sendall((command + "\n").encode())
        reply = b""
        while b"\n" not in reply:
            part = s.recv(8192)
            if not part:
                raise RuntimeError("control disconnected")
            reply += part
        return reply.decode().strip()


old_timeout = adb("shell", "settings", "get", "system", "screen_off_timeout")
record = None
samples = []
try:
    (OUT / "install.log").write_text(adb("install", "--no-incremental", "-r", str(APK), timeout=120))
    adb("shell", "am", "force-stop", PKG)
    adb("shell", "settings", "put", "system", "screen_off_timeout", "120000")
    adb("shell", "input", "keyevent", "KEYCODE_WAKEUP")
    adb("shell", "wm", "dismiss-keyguard")
    adb("shell", "am", "start", "-n", PKG + "/.LeanActivity")
    adb("forward", "tcp:" + str(PORT), "localabstract:leanquiet")
    for attempt in range(30):
        try:
            if ctl("ping") == "pong":
                break
        except (OSError, RuntimeError):
            time.sleep(.2)
    else:
        raise RuntimeError("app control did not become ready")
    ctl("channel")
    ctl("bottom")
    time.sleep(3)
    initial = ctl("state")
    assert "total 0 " not in initial, "requires a provisioned conversation"
    (OUT / "initial.txt").write_text(initial)
    record = subprocess.Popen(ADB + ["shell", "screenrecord", "--time-limit", "20", "/data/local/tmp/quiet-scroll.mp4"])
    start = time.monotonic()
    for offset in [0, 2000, 4000, 6000, 8000, 10000, 12000, 14000, 16000, 18000,
                   16000, 14000, 12000, 10000, 8000, 10000, 12000, 14000, 16000, 18000]:
        t = time.monotonic()
        ctl("scroll " + str(offset))
        samples.append({"offset": offset, "at_ms": (t-start)*1000,
                        "reply_ms": (time.monotonic()-t)*1000})
        time.sleep(.08)
    stopped = time.monotonic()
    for _ in range(12):
        time.sleep(.1)
        samples.append({"after_stop_ms": (time.monotonic()-stopped)*1000,
                        "state": ctl("state"), "stats": ctl("stats")})
    with (OUT / "stopped.png").open("wb") as f:
        subprocess.run(ADB + ["exec-out", "screencap", "-p"], stdout=f, check=True, timeout=15)
    print(samples[-1], flush=True)
    assert record.wait(timeout=30) == 0, "screen recording failed"
    record = None
    adb("pull", "/data/local/tmp/quiet-scroll.mp4", str(OUT / "scroll.mp4"))
    adb("shell", "rm", "/data/local/tmp/quiet-scroll.mp4")
    result["passed"] = True
finally:
    (OUT / "samples.json").write_text(json.dumps(samples, indent=2))
    (OUT / "result.json").write_text(json.dumps(result, indent=2))
    try:
        if record is not None:
            record.wait(timeout=30)
        (OUT / "logcat.txt").write_text(adb("logcat", "-d", "-t", "5000"))
    finally:
        adb("shell", "settings", "put", "system", "screen_off_timeout", old_timeout)
