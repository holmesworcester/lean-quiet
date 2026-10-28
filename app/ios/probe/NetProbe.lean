/-
What lean-quiet's networking needs from inside an iOS app, in the
Simulator or on an iPhone, as three separate results:

1. **lean-mdns raw multicast**: mDNS over Lean's own UDP socket (Mdns.Net:
   port 5353 shared with the system's responder, group 224.0.0.251).
   Announce <instance> of type `_leanquiet._udp` every second (the harness
   checks the Mac sees it with `dns-sd -B` and `dns-sd -L`) while browsing
   that type, logging each service found (the harness registers `probe`
   with `dns-sd -R`).
2. **dns_sd**: the system's DNS-SD (dnssd.c over dns_sd.h; no multicast
   entitlement needed): register <instance>-sd, browse the type, and
   resolve each service found to host, port and IPv4 addresses, which
   come back to Lean (Sd.poll). Lean then connects over TCP to the address
   it resolved for the Mac's `probe` (tcp-dnssd): discovery by the system,
   everything after it by Lean.
3. **TCP**: connect to <host>:<port> (the harness's echo listener on the
   Mac), and listen on 0.0.0.0:<port + 1> for the harness to connect.

Announcements carry only the Wi-Fi address (en0 on iOS and macOS, wl* on
Linux): the others (Tailscale, bridges) are not reachable from the LAN.

Every step is bounded in time (a blocked network must not hang the probe)
and prints `ok <step> ...` or `fail <step> ...` on stderr, then a summary
line per result (`result <name>: ok|fail`); the exit code is the number of
failed results.

    NetProbe <host> <port> <seconds> <instance>
-/
import Mdns
import Std.Async.TCP
open Mdns Std.Async Std.Net

namespace Sd

/-- Registers `name` of `type` on `port` with the system's responder. -/
@[extern "lq_sd_register"] opaque register (name type : @& String) (port : UInt16) : IO Unit

/-- Browses `type`: every service found is resolved to its host, port and
IPv4 addresses (as events). -/
@[extern "lq_sd_browse"] opaque browse (type : @& String) : IO Unit

/-- The events since the last call, each `#[kind, name, host, port, addr]`:
"registered" (name), "found" (name, host, port, one address), "error"
(name = what failed, host = dns_sd's code). -/
@[extern "lq_sd_poll"] opaque poll : IO (Array (Array String))

end Sd

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

/-- The Wi-Fi interface's IPv4 addresses: en0 (iOS, macOS) or wl* (Linux);
every non-loopback one if there is no such interface. -/
def wifiAddrs : IO (List (List UInt8)) := do
  let xs := (← interfaceAddresses).toList.filterMap fun i =>
    if i.isLoopback then none else
    match i.address with
    | .v4 a => some (i.name, a.octets.toList)
    | .v6 _ => none
  let wifi := xs.filter fun (n, _) => n == "en0" || n.startsWith "wl"
  pure ((if wifi.isEmpty then xs else wifi).map (·.2))

/-- Result 1: announces `inst` and browses for `secs`; true if a service
was found and every send went out. -/
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

/-- A service the system's DNS-SD resolved: name, host, port, address. -/
structure SdFound where
  name : String
  host : String
  port : Nat
  addr : String

/-- Result 2, started: registers `<inst>-sd` and browses; a dedicated task
takes the events as they come (printing each) into `found`, and records
whether registering worked and any error. -/
def sdStart (inst : String) (found : IO.Ref (Array SdFound)) (registered failed : IO.Ref Bool) :
    IO Unit := do
  match ← (do Sd.register s!"{inst}-sd" "_leanquiet._udp" 7401; Sd.browse "_leanquiet._udp").toBaseIO with
  | .ok () => pure ()
  | .error e => say s!"fail dnssd-start: {e}"; failed.set true
  let _ ← IO.asTask (prio := .dedicated) do
    repeat
      for ev in ← Sd.poll do
        match ev.toList with
        | ["registered", n, _, _, _] =>
          registered.set true
          say s!"ok dnssd-registered {n}"
        | ["found", n, h, p, a] =>
          found.modify (·.push ⟨n, h, p.toNat!, a⟩)
          say s!"ok dnssd-found {n} host {h} port {p} addr {a}"
        | ["error", what, code, _, _] =>
          failed.set true
          say s!"fail dnssd-{what}: error {code}"
        | _ => pure ()
      IO.sleep 200

/-- One TCP exchange as the client: connect, send a line, read the echo. -/
def echoOut (step : String) (to : IPv4Addr) (port : UInt16) : IO Bool := do
  let out ← within 15000 (do
    let c ← TCP.Socket.Client.mk
    c.connect (.v4 ⟨to, port⟩)
    c.send s!"{step}\n".toUTF8
    let r ← c.recv? 64
    c.shutdown
    pure r : Async (Option ByteArray)).block
  match out with
  | some (.ok (some r)) => say s!"ok {step} echo {repr (String.fromUTF8? r)}"; pure true
  | some (.ok none) => say s!"fail {step}: closed with no reply"; pure false
  | some (.error e) => say s!"fail {step}: {e}"; pure false
  | none => say s!"fail {step}: no answer in 15 s"; pure false

/-- TCP in: listen on port, echo one line from the harness. -/
def echoIn (port : UInt16) : IO Bool := do
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  srv.listen 4
  say s!"listening on {port}"
  let inn ← within 30000 (do
    let c ← srv.accept
    let r ← c.recv? 64
    if let some b := r then c.send b
    c.shutdown
    pure r : Async (Option ByteArray)).block
  match inn with
  | some (.ok (some r)) => say s!"ok tcp-in got {repr (String.fromUTF8? r)}"; pure true
  | some (.ok none) => say "fail tcp-in: closed with nothing"; pure false
  | some (.error e) => say s!"fail tcp-in: {e}"; pure false
  | none => say "fail tcp-in: no connection in 30 s"; pure false

/-- The address Lean picks for the Mac's `probe` (or `probe (2)`, …) among
what the system resolved: one on our Wi-Fi's /24 first. -/
def pickProbe (found : Array SdFound) (wifi : List (List UInt8)) : Option IPv4Addr :=
  let mine := found.filter fun f => f.name == "probe" || f.name.startsWith "probe ("
  let net (a : String) := ".".intercalate ((a.splitOn ".").take 3)
  let nets := wifi.map fun a => net (showAddr a)
  let pick := (mine.find? fun f => nets.contains (net f.addr)) <|> (mine.find? fun f => f.addr != "127.0.0.1")
  pick >>= fun f => v4 f.addr

def main (args : List String) : IO UInt32 := do
  let host := (args[0]? >>= v4).getD (IPv4Addr.ofParts 127 0 0 1)
  let port := ((args[1]? >>= String.toNat?).getD 7420).toUInt16
  let secs := (args[2]? >>= String.toNat?).getD 15
  let inst := args[3]?.getD "lean-ios-probe"
  let addrs ← wifiAddrs
  say s!"ok addrs {" ".intercalate (addrs.map showAddr)} (the Wi-Fi's, announced)"
  let found ← IO.mkRef (#[] : Array SdFound)
  let registered ← IO.mkRef false
  let sdFailed ← IO.mkRef false
  sdStart inst found registered sdFailed
  let r1 ← match ← (mdns inst secs addrs).toBaseIO with
    | .ok ok => pure ok
    | .error e => do say s!"fail mdns: {e}"; pure false
  -- result 2: registered, and the Mac's probe resolved to an address Lean
  -- then reaches over TCP
  let viaSd ← match pickProbe (← found.get) addrs with
    | some a => echoOut "tcp-dnssd" a port
    | none => do say "fail tcp-dnssd: dns_sd resolved no address for the Mac's probe"; pure false
  let r2 := (← registered.get) && !(← sdFailed.get) && viaSd
  -- result 3
  let out ← echoOut "tcp-out" host port
  let inn ← echoIn (port + 1)
  let r3 := out && inn
  let verdict (b : Bool) := if b then "ok" else "fail"
  say s!"result lean-mdns raw multicast: {verdict r1}"
  say s!"result dns_sd register/browse/resolve (+ Lean TCP to what it resolved): {verdict r2}"
  say s!"result TCP to the Mac (out) and from it (in): {verdict r3}"
  let fails := [r1, r2, r3].filter (!·) |>.length
  say s!"done {fails} failed"
  -- (Lean would wait at exit for the dedicated tasks still running)
  IO.Process.exit fails.toUInt8
