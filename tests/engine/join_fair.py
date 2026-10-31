#!/usr/bin/env python3
"""Control real TCP traffic for JoinFair; retain SQLite files, logs and relay stats.

Linux localhost sockets, Python3, the Lean native runtime and production crypto
archive are required. The named Mise task builds them before invoking this file.
This bounded regression makes no claim about infinite schedules or OS fairness.
"""
import argparse
import json
import pathlib
import select
import socket
import subprocess
import threading
import time


class Relay:
    def __init__(self, directory, target_name, stats_name):
        self.directory = directory
        self.target_name = target_name
        self.stats_name = stats_name
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(16)
        self.listener.setblocking(False)
        self.port = self.listener.getsockname()[1]
        self.stopping = threading.Event()
        self.pairs = {}
        self.pending = {}
        self.slow_sources = set()
        self.slow_targets = set()
        self.next_send = {}
        self.stats = dict(connections=0, disconnected=0, bytes_forwarded=0,
                          paused_readable=0, peak_buffer=0, forced_disconnects=0,
                          reconnects=0, connect_failures=0, throttled_bytes=0,
                          throttled_buffered_steps=0, backpressure_read_pauses=0)
        self.saw_disconnect = False
        self.error = None
        self.thread = threading.Thread(target=self.run, daemon=True)

    def close_pair(self, stream):
        other = self.pairs.pop(stream, None)
        if other is not None:
            self.pairs.pop(other, None)
            self.pending.pop(other, None)
            other.close()
            self.slow_sources.discard(other)
            self.slow_targets.discard(other)
            self.next_send.pop(other, None)
        self.pending.pop(stream, None)
        stream.close()
        self.slow_sources.discard(stream)
        self.slow_targets.discard(stream)
        self.next_send.pop(stream, None)
        self.stats["disconnected"] += 1

    def run(self):
        mode = "pause"
        try:
            while not self.stopping.is_set():
                try:
                    mode = (self.directory / "relay-mode").read_text().strip() or mode
                except FileNotFoundError:
                    pass
                if mode == "disconnect":
                    self.saw_disconnect = True
                    for stream in list(self.pairs):
                        if stream in self.pairs:
                            self.stats["forced_disconnects"] += 1
                            self.close_pair(stream)
                if mode == "backpressure":
                    self.stats["throttled_buffered_steps"] += int(any(
                        self.pending[s] for s in self.slow_targets))
                    self.stats["backpressure_read_pauses"] += sum(
                        len(self.pending[self.pairs[s]]) >= 65536 for s in self.slow_sources)
                forwarding = mode in ("open", "backpressure")
                readable = [self.listener] + [s for s in self.pairs
                    if not forwarding or len(self.pending[self.pairs[s]]) < 65536]
                writable = [s for s in self.pairs if forwarding and self.pending[s] and
                    (mode != "backpressure" or s not in self.slow_targets or
                     time.monotonic() >= self.next_send.get(s, 0))]
                reads, writes, _ = select.select(readable, writable, [], .01)
                for stream in reads:
                    if stream is self.listener:
                        incoming, _ = self.listener.accept()
                        if mode == "disconnect":
                            incoming.close()
                            continue
                        outgoing = socket.socket()
                        # A small receive window makes a paused relay propagate
                        # real socket backpressure rather than absorb a huge copy.
                        outgoing.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
                        outgoing.settimeout(2)
                        try:
                            outgoing.connect(("127.0.0.1", int((self.directory / self.target_name).read_text())))
                        except OSError:
                            self.stats["connect_failures"] += 1
                            incoming.close()
                            outgoing.close()
                            continue
                        for s in (incoming, outgoing):
                            s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                            s.setblocking(False)
                            self.pending[s] = bytearray()
                        self.pairs[incoming] = outgoing
                        self.pairs[outgoing] = incoming
                        source = outgoing if self.target_name == "target-port" else incoming
                        self.slow_sources.add(source)
                        self.slow_targets.add(self.pairs[source])
                        self.stats["connections"] += 1
                        if self.saw_disconnect:
                            self.stats["reconnects"] += 1
                    elif stream in self.pairs:
                        if not forwarding:
                            self.stats["paused_readable"] += 1
                            continue
                        try:
                            data = stream.recv(16384)
                        except BlockingIOError:
                            continue
                        except (ConnectionResetError, OSError):
                            data = b""
                        if not data:
                            self.close_pair(stream)
                        else:
                            target = self.pairs[stream]
                            self.pending[target].extend(data)
                            self.stats["peak_buffer"] = max(self.stats["peak_buffer"], len(self.pending[target]))
                for stream in writes:
                    if stream not in self.pairs:
                        continue
                    try:
                        slow = mode == "backpressure" and stream in self.slow_targets
                        sent = stream.send(self.pending[stream][:512] if slow else self.pending[stream])
                        del self.pending[stream][:sent]
                        self.stats["bytes_forwarded"] += sent
                        if slow:
                            self.stats["throttled_bytes"] += sent
                            self.next_send[stream] = time.monotonic() + .01
                    except BlockingIOError:
                        continue
                    except (ConnectionResetError, BrokenPipeError, OSError):
                        self.close_pair(stream)
                if not forwarding:
                    time.sleep(.01)
        except BaseException as error:
            self.error = repr(error)
        finally:
            for stream in list(self.pairs):
                if stream in self.pairs:
                    self.close_pair(stream)
            self.listener.close()
            (self.directory / self.stats_name).write_text(json.dumps(self.stats, indent=2) + "\n")


def free_ports():
    held = []
    try:
        for _ in range(2):
            s = socket.socket()
            s.bind(("127.0.0.1", 0))
            held.append(s)
        return [s.getsockname()[1] for s in held]
    finally:
        for s in held:
            s.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=pathlib.Path, default=pathlib.Path(".lake/build/bin/join_fair"))
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("out/join-fair/baseline"))
    parser.add_argument("--expect-starvation", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "relay-mode").write_text("pause")
    a_port, b_port = free_ports()
    (args.out / "target-port").write_text(str(a_port))
    (args.out / "target-port-b").write_text(str(b_port))
    relays = [Relay(args.out, "target-port", "relay-a.json"),
              Relay(args.out, "target-port-b", "relay-b.json")]
    for relay in relays:
        relay.thread.start()
    command = [str(args.binary.resolve()), str(args.out.resolve()), str(relays[0].port),
               str(a_port), str(b_port), str(relays[1].port)]
    log_path = args.out / "runner.log"
    try:
        with log_path.open("w") as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=90)
        text = log_path.read_text()
    except subprocess.TimeoutExpired:
        raise SystemExit(f"join-fair timed out; retained {log_path}")
    finally:
        for relay in relays:
            relay.stopping.set()
        for relay in relays:
            relay.thread.join(timeout=3)
    print(text, end="", flush=True)
    if any(relay.error for relay in relays):
        raise SystemExit(f"relay failed: {[r.error for r in relays]}; see {args.out}")
    if any(relay.thread.is_alive() for relay in relays):
        raise SystemExit(f"relay thread failed to stop; see {args.out}")
    if any(marker in text for marker in ["PANIC", "panic", "network runner stopped:", "join-fair exception:"]):
        raise SystemExit(f"native/runtime failure; see {log_path}")
    if args.expect_starvation:
        expected = "FAIL: peer message progresses while write queue stays nonempty"
        failures = [line for line in text.splitlines() if line.startswith("FAIL:")]
        if result.returncode == 0 or failures != [expected]:
            raise SystemExit(f"strict-priority control survived or failed for another reason; see {log_path}")
        print("strict-priority control rejected by actual peer-message starvation assertion")
    elif result.returncode != 0:
        raise SystemExit(f"join-fair failed ({result.returncode}); see {log_path}")
    elif sum(r.stats["connections"] for r in relays) < 2 or sum(r.stats["paused_readable"] for r in relays) == 0:
        raise SystemExit(f"relay did not exercise delay/disconnect/reconnect; see {args.out}")
    elif any(sum(r.stats[name] for r in relays) == 0 for name in
             ["forced_disconnects", "reconnects", "throttled_bytes", "backpressure_read_pauses"]):
        raise SystemExit(f"required actual throttle/disconnect/reconnect evidence missing; see {args.out}")
    elif sum(r.stats["throttled_buffered_steps"] for r in relays) < 2:
        raise SystemExit(f"throttle never retained buffered traffic across steps; see {args.out}")


if __name__ == "__main__":
    main()
