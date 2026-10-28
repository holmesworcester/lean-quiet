#!/usr/bin/env python3
"""The probe's peer for its TCP steps (NetProbe.lean), on the Mac:

    harness.py PORT BIND TARGET

an echo listener on BIND:PORT for one connection (the probe's TCP out)
and, at the same time, connection attempts to TARGET:PORT+1 (its TCP in)
for up to two minutes. TARGET is an address, or @FILE: the probe's
console log, whose `ok addrs` line gives the probe's addresses; the one on
BIND's /24 is used (an iPhone on the Mac's Wi-Fi)."""
import socket, sys, threading, time

port, bind, target = int(sys.argv[1]), sys.argv[2], sys.argv[3]

def echo():
    srv = socket.socket()
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind((bind, port))
    srv.listen(1)
    srv.settimeout(120)
    try:
        c, peer = srv.accept()
        d = c.recv(64)
        c.sendall(d)
        c.close()
        print("harness: echoed", d, "from", peer[0], flush=True)
    except socket.timeout:
        print("harness: the probe never connected", flush=True)
    srv.close()

def addr():
    if not target.startswith("@"):
        return target
    net = bind.rsplit(".", 1)[0] + "."
    try:
        for line in open(target[1:], errors="replace"):
            if line.startswith("ok addrs"):
                for a in line.split()[2:]:
                    if a.startswith(net):
                        return a
    except OSError:
        pass
    return None

t = threading.Thread(target=echo)
t.start()
end = time.time() + 120
while time.time() < end:
    a = addr()
    if a:
        try:
            s = socket.create_connection((a, port + 1), timeout=3)
            s.sendall(b"probe in\n")
            print("harness: got back", s.recv(64), "from", a, flush=True)
            s.close()
            break
        except OSError:
            pass
    time.sleep(0.3)
else:
    print("harness: could not connect to the probe's listener", flush=True)
t.join()
