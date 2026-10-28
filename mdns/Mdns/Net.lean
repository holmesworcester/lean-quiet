/-
mDNS on the network: one UDP socket on port 5353, in the IPv4 group
224.0.0.251, over Lean's own Std.Async.UDP (libuv). The socket shares the
port with the system's responder (avahi, mDNSResponder, adb), since Lean
binds it with UV_UDP_REUSEADDR.

    let sock ← Mdns.Net.open
    Mdns.Net.send sock (Mdns.announce me)       -- tell the network
    Mdns.Net.send sock (Mdns.query "_leanquiet._udp")
    Mdns.Net.loop sock [me] ["_leanquiet._udp"] fun f => IO.println f.inst

`loop` answers questions about `self` and hands every service of the
browsed types that an answer mentions to `onFound`, until `stop` says so
(it is checked after each packet). Sending from another task while `loop`
runs is fine. A packet that does not decode is dropped.

On Android, take a WifiManager.MulticastLock first, or the Wi-Fi driver
may drop incoming multicast.
-/
import Std.Async.UDP
import Mdns.Decode
import Mdns.Service

namespace Mdns.Net

open Std.Async Std.Net

def group : IPv4Addr := IPv4Addr.ofParts 224 0 0 251
def port : UInt16 := 5353
def groupAddr : SocketAddress := .v4 ⟨group, port⟩

def «open» : IO UDP.Socket := do
  let s ← UDP.Socket.mk
  s.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  s.setMembership (.v4 group) none .enterGroup
  s.setMulticastTTL 255
  s.setMulticastLoop true
  pure s

def send (s : UDP.Socket) (m : Msg) : Async Unit := s.send (encode m) (some groupAddr)

def loop (s : UDP.Socket) (self : List Service) (browse : List String)
    (onFound : Found → IO Unit) (stop : IO Bool := pure false) : Async Unit := do
  repeat
    let (pkt, _) ← s.recv 9000
    if let some m := decode pkt then
      if let some r := react self m then send s r
      for t in browse do
        for f in found t m do
          unless self.any (fun me => me.type == t && me.inst == f.inst) do
            onFound f
    if ← stop then break

/-- This machine's non-loopback addresses, as A/AAAA rdata. -/
def localAddrs : IO (List (List UInt8)) := do
  let xs ← interfaceAddresses
  pure <| xs.toList.filterMap fun i =>
    if i.isLoopback then none else
    match i.address with
    | .v4 a => some a.octets.toList
    | .v6 _ => none

end Mdns.Net
