/-
What lean-quiet's networking needs from inside an iOS app, probed with
Lean's own sockets (Std.Async over libuv, as the app's network will use
them), in the Simulator or on an iPhone:

1. The interfaces' IPv4 addresses (what an announcement carries).
2. mDNS over UDP multicast with lean-mdns (Mdns.Net: port 5353 shared
   with the system's responder, group 224.0.0.251): announce <instance> of
   type `_leanquiet._udp` every second (the harness checks the Mac sees
   it, `dns-sd -B` and `dns-sd -L`) while browsing that type, logging each
   service found once (the harness registers `probe` with `dns-sd -R`):
   multicast out and in.
3. TCP out: connect to <host>:<port> (the harness's echo listener), send a
   line, read the echo.
4. TCP in: listen on 0.0.0.0:<port + 1>; the harness connects and sends a
   line, the probe echoes it.

Every step is bounded in time (a blocked network must not hang the probe)
and prints `ok <step> ...` or `fail <step> ...` on stderr; the exit code
is the number of failures.

    NetProbe <host> <port> <seconds> <instance>
-/
import Mdns
import Std.Async.TCP
open Mdns Std.Async Std.Net

def say (s : String) : IO Unit := do
  IO.eprintln s
  (← IO.getStderr).flush

def showAddr (a : List UInt8) : String := ".".intercalate (a.map (toString ·.toNat))

/-- act on a dedicated task, waited for at most ms: none if it is still
running then. -/
def within (ms : Nat) (act : IO α) : IO (Option (Except IO.Error α)) := do
  let t ← IO.asTask (prio := .dedicated) act
  let deadline := (← IO.monoMsNow) + ms
  while !(← IO.hasFinished t) && (← IO.monoMsNow) < deadline do
    IO.sleep 50
  if ← IO.hasFinished t then return some t.get else return none

def v4 (s : String) : Option IPv4Addr :=
  match (s.splitOn ".").map String.toNat? with
  | [some a, some b, some c, some d] => some (IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8)
  | _ => none

/-- Step 2: announces `inst` and browses for `secs`; true if anything else
of the type was found and every send went out. -/
def mdns (inst : String) (secs : Nat) (addrs : List (List UInt8)) : IO Bool := do
  let s ← Net.open
  say "ok mdns-open (udp 5353 bound with the system's responder, 224.0.0.251 joined)"
  let me : Service := { inst, type := "_leanquiet._udp", host := inst, port := 7400,
                        txt := ["impl=lean-mdns", "probe=1"], addrs }
  let deadline := (← IO.monoMsNow) + secs * 1000
  let seen ← IO.mkRef ([] : List String)
  let sent ← IO.mkRef (0 : Nat)
  let failed ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    while (← IO.monoMsNow) < deadline do
      match ← (do (Net.send s (announce me)).block; (Net.send s (query "_leanquiet._udp")).block).toBaseIO with
      | .ok () => sent.modify (· + 1)
      | .error e =>
        unless ← failed.get do
          failed.set true
          say s!"fail mdns-send: {e}"
      IO.sleep 1000
    let _ ← (Net.send s (goodbye me)).block.toBaseIO
  -- The loop never ends by itself (it waits for a packet): it is left
  -- running, and the process exits.
  let _ ← IO.asTask (prio := .dedicated) do
    let r ← (Net.loop s [me] ["_leanquiet._udp"] fun f => do
      if f.ttl != 0 && !(← seen.get).contains f.inst then
        seen.modify (f.inst :: ·)
        say s!"ok mdns-found {f.inst} host {f.host} port {f.port} txt {",".intercalate f.txt} addrs {" ".intercalate (f.addrs.map showAddr)}").block.toBaseIO
    if let .error e := r then say s!"fail mdns-recv: {e}"
  IO.sleep (secs * 1000).toUInt32
  say s!"mdns: {← sent.get} rounds of announcement and query sent, {(← seen.get).length} services found"
  pure (!(← seen.get).isEmpty && !(← failed.get))

/-- Steps 3 and 4: how many failed. -/
def tcp (host : IPv4Addr) (port : UInt16) : IO Nat := do
  let mut fails := 0
  let out ← within 15000 (do
    let c ← TCP.Socket.Client.mk
    c.connect (.v4 ⟨host, port⟩)
    c.send "probe out\n".toUTF8
    let r ← c.recv? 64
    c.shutdown
    pure r : Async (Option ByteArray)).block
  match out with
  | some (.ok (some r)) => say s!"ok tcp-out echo {repr (String.fromUTF8? r)}"
  | some (.ok none) => say "fail tcp-out: closed with no reply"; fails := fails + 1
  | some (.error e) => say s!"fail tcp-out: {e}"; fails := fails + 1
  | none => say "fail tcp-out: no answer in 15 s"; fails := fails + 1
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port + 1⟩)
  srv.listen 4
  say s!"listening on {port + 1}"
  let inn ← within 30000 (do
    let c ← srv.accept
    let r ← c.recv? 64
    if let some b := r then c.send b
    c.shutdown
    pure r : Async (Option ByteArray)).block
  match inn with
  | some (.ok (some r)) => say s!"ok tcp-in got {repr (String.fromUTF8? r)}"
  | some (.ok none) => say "fail tcp-in: closed with nothing"; fails := fails + 1
  | some (.error e) => say s!"fail tcp-in: {e}"; fails := fails + 1
  | none => say "fail tcp-in: no connection in 30 s"; fails := fails + 1
  pure fails

def main (args : List String) : IO UInt32 := do
  let host := (args[0]? >>= v4).getD (IPv4Addr.ofParts 127 0 0 1)
  let port := ((args[1]? >>= String.toNat?).getD 7420).toUInt16
  let secs := (args[2]? >>= String.toNat?).getD 15
  let inst := args[3]?.getD "lean-ios-probe"
  let mut fails := 0
  let addrs ← Net.localAddrs
  say s!"ok addrs {" ".intercalate (addrs.map showAddr)}"
  match ← (mdns inst secs addrs).toBaseIO with
  | .ok true => pure ()
  | .ok false => say "fail mdns: nothing found, or sending failed"; fails := fails + 1
  | .error e => say s!"fail mdns: {e}"; fails := fails + 1
  fails := fails + (← tcp host port)
  say s!"done {fails} failed"
  -- (Lean would wait at exit for the dedicated tasks still running)
  IO.Process.exit fails.toUInt8
