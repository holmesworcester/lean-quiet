import tests.endpoints.Harness
import ops.connection.DiscoveryLaws

open Engine Community Connection EndpointNetwork

def require (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"ok: {name}" else throw (IO.userError s!"FAIL: {name}")

def ad (detected observed : List ByteArray) (time expires : Nat) (signer : Device := dev "A") : Op :=
  let reqs := [c, c]
  let b : Community.Body := .addresses detected observed time expires .empty
  Community.mkOp reqs (.addresses detected observed time expires (Community.sig signer.sk reqs b))

def accepted (o : Op) : Bool :=
  (Community.validate ed25519 o [.admission c c (dev "A").pk (key "A"),
    .admission c c (dev "A").pk (key "A")]).isSome

def main : IO Unit := do
  let lan := "192.168.4.35:47100".toUTF8
  let tail := "100.67.2.56:47100".toUTF8
  let good := ad [lan] [tail] 1000 2000
  require "actual Ed25519 endpoint-op acceptance witness" (accepted good)
  require "another member cannot author A's endpoint op" (!accepted (ad [lan] [] 1000 2000 (dev "B")))
  require "nine addresses are rejected at validation" (!accepted (ad (List.replicate 9 lan) [] 1000 2000))
  require "lifetime beyond five minutes is rejected" (!accepted (ad [lan] [] 1000 301001))
  require "zero lifetime is rejected" (!accepted (ad [lan] [] 1000 1000))
  require "multicast destinations are rejected" (!accepted (ad ["224.0.0.251:5353".toUTF8] [] 1000 2000))
  require "zero TCP port is rejected" (!accepted (ad ["100.67.2.56:0".toUTF8] [] 1000 2000))
  require "expiry is strict" (!Endpoint.fresh 2000 1000 2000)
  require "future publication is not dialable" (!Endpoint.fresh 900 1000 2000)
  require "updated endpoint data does not reset retry clock"
    (!Discovery.canTry 1200 (some (1000, 5)))
  require "backoff releases by 60 seconds" (Discovery.canTry 61000 (some (1000, 500)))
  let hints := Link.hints [("docker0", [172,17,0,1], false), ("br-test", [192,168,80,1], false),
    ("wlan0", [192,168,4,35], false), ("tailscale0", [100,67,2,56], false)]
  require "invites carry LAN and tailnet, excluding Docker bridges" (hints == [lan, tail])
  require "repeated interface addresses coalesce" ((Link.hints [("wlan0", [192,168,4,35], false),
    ("wlan1", [192,168,4,35], false)]).length == 1)
  let req := Community.issue c c (dev "A") (key "A") (seed "invite") hints
  require "multi-address invite roundtrips through the actual link parser"
    (Community.Invite.parse req.2.text == some req.2)
  let db ← Db.openAt ":memory:"
  (Engine.receive fam (shared ++ [good, ad [] [] 2001 2100]) : SqlM F Unit).run db
  let current ← ((Discovery.advertised c (key "A") 2200).run : SqlM F _).run db
  require "an expired latest op never resurrects older addresses" current.isEmpty
  let svc := DiscoveryNet.service (key "A") 47100 [Std.Net.IPv4Addr.ofParts 100 67 2 56]
  let query := Mdns.unicastQuery DiscoveryNet.serviceType
  let some (reply, unicast) := Mdns.response [svc] query 5353 | throw (IO.userError "no DNS-SD reply")
  require "routed DNS-SD asks for and receives unicast" unicast
  let found := Mdns.found DiscoveryNet.serviceType reply
  require "same DNS-SD result maps to a bounded endpoint op" ((found.head?.bind (DiscoveryNet.foundOp · 1000)).isSome)
  require "malformed key cannot become a discovery op" ((DiscoveryNet.foundOp { inst := "bad", host := "bad", port := 1, txt := ["key=00"], addrs := [], ttl := 120 } 1000).isNone)
  IO.println "PASS endpoint validation, source selection, expiry and DNS-SD checks"
