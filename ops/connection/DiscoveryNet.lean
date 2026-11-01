/- Native discovery adapter. DNS-SD is only an address hint: the invite or
membership supplies the peer identity and Noise authenticates the connection.
One worker, a bounded datagram, rate-limited observations, cancellable receive.
The worker never dials: it submits ops to the same runner as app writes. -/
import ops.connection.Discovery
import ops.community.link.View
import engine.wire.mdns.Unicast
import engine.wire.Tcp
import Std.Time.DateTime.Timestamp

namespace Connection.DiscoveryNet
open Engine Engine.Sync Std.Async Std.Net

def serviceType : String := "_leanquiet._tcp"

def wallNow : IO Nat := do
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat

def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length = 1 then "0" ++ s else s)

def hexDigit (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

def unhex (s : String) : Option ByteArray := do
  if s.length != 64 then none else do
    let chars := s.toList.toArray
    let mut out := ByteArray.empty
    for i in [:32] do
      let a ← hexDigit chars[i*2]!
      let b ← hexDigit chars[i*2+1]!
      out := out.push (a*16+b).toUInt8
    return out

def service (pk : ByteArray) (port : UInt16) (ips : List IPv4Addr) : Mdns.Service :=
  let name := "quiet-" ++ ((hex pk).take 48).toString
  { inst := name, type := serviceType, host := name, port,
    txt := ["key=" ++ hex pk], addrs := ips.take 8 |>.map (·.octets.toList) }

/-- Restrict received endpoint lists before persisting them. TTL 0 withdraws. -/
def foundOp (f : Mdns.Found) (now : Nat) : Option Op := do
  let txt ← f.txt.find? (·.startsWith "key=")
  let pk ← unhex (txt.drop 4 |>.toString)
  let hs := Endpoint.bounded (f.addrs.take 8 |>.filterMap fun bytes =>
    if bytes.length = 4 then
      some ((String.intercalate "." (bytes.map (toString ·.toNat)) ++ ":" ++ toString f.port).toUTF8)
    else none)
  return Community.mkOp [] (.discovered pk hs now (min Endpoint.maxAge (f.ttl.toNat * 1000)))

/-- Poll the native promise on the dedicated worker, matching TCP's
`readSocket`. Cancelling a silent read releases it before shutdown; no task
pool continuation retains an outstanding UDP receive. -/
def receive (s : UDP.Socket) (stopped : IO.Ref Bool) : IO (Option (ByteArray × Option SocketAddress)) := do
  let p ← s.native.recv 9000
  let deadline := (← IO.monoMsNow) + 1000
  repeat
    if (← stopped.get) || (← IO.monoMsNow) ≥ deadline then
      s.native.cancelRecv
      return none
    if ← p.isResolved then
      match ← IO.wait p.result? with
      | some (.ok packet) => return some packet
      | _ => return none
    IO.sleep 10

def send (s : UDP.Socket) (m : Mdns.Msg) (target : SocketAddress) : IO Unit := do
  discard <| IO.ofExcept (← awaitUv (s.native.send #[Mdns.encode m] (some target)))

/-- The remote seeds are explicit known tailnet IPv4 addresses, never a scan
of the /10. The app also learns tailnet seeds through invite/endpoint ops. -/
def run (r : Runner) (db : Db) (tailnet : List IPv4Addr := []) : IO Unit := do
  let sock ← UDP.Socket.mk
  IO.eprintln "discovery: UDP socket created"
  sock.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, 5353⟩)
  IO.eprintln "discovery: UDP 5353 bound"
  -- Join only the explicit LAN interfaces below. Android may reject a
  -- default-interface multicast join when its default route is cellular.
  sock.setMulticastTTL 255
  sock.setMulticastLoop true
  let mut last := 0
  let mut offered : List Mdns.Service := []
  let mut routed : List Mdns.Service := []
  let mut me := ByteArray.empty
  let mut joined : List IPv4Addr := []
  while !(← r.stopped.get) do
    let now ← wallNow
    if now ≥ last + 15000 then
      last := now
      if let some (pk, _, _) := (← (endpoints : SqlM F _).run db).head? then
        me := pk
        IO.eprintln "discovery: reading interfaces"
        let addrs ← Link.local?
        let hints := Link.hints addrs r.port.toNat
        IO.eprintln s!"discovery: detected {hints.map (fun b => (String.fromUTF8? b).getD "?")}"
        let ips := hints.filterMap fun h => (Endpoint.parse h).map (·.1)
        let lan := ips.filter fun ip => Link.isPrivate (ip.octets.toList.map (·.toNat))
        offered := [service pk r.port lan]
        routed := [service pk r.port (ips.filter fun ip => Link.isTailnet (ip.octets.toList.map (·.toNat)))]
        discard <| r.writes.trySend [Community.mkOp [] (.discovered pk hints now Endpoint.maxAge)]
        -- Set the outgoing multicast interface explicitly; never a Docker bridge.
        for ip in lan do
          unless joined.contains ip do
            try
              sock.setMembership (.v4 Mdns.Net.group) (some (.v4 ip)) .enterGroup
              IO.eprintln s!"discovery: joined {ip}"
            catch e => IO.eprintln s!"discovery: join {ip}: {e}"
            joined := (ip :: joined).take 8
          IO.eprintln s!"discovery: selecting {ip}"
          sock.setMulticastInterface (.v4 ip)
          IO.eprintln "discovery: announcing"
          send sock (Mdns.announce offered.head!) Mdns.Net.groupAddr
          IO.eprintln "discovery: querying"
          send sock (Mdns.query serviceType) Mdns.Net.groupAddr
          IO.eprintln "discovery: query sent"
        let hints ← ((Discovery.readCommunity Community.discoveryHints [] 8).run : SqlM F _).run db
        let seeds := hints.flatMap fun (_, fact) => match fact with
          | .joining _ _ hs .. => hs.take 8
          | .addresses _ _ ds os issued expires => if Endpoint.fresh now issued expires then ds ++ os else []
          | _ => []
        let seeds := seeds.filterMap fun h => (Endpoint.parse h).map (·.1)
        let seeds := seeds.filter fun ip => Link.isTailnet (ip.octets.toList.map (·.toNat))
        for ip in (tailnet ++ seeds).eraseDups.take 8 do
          send sock (Mdns.unicastQuery serviceType) (.v4 ⟨ip, 5353⟩)
    if let some (bytes, source) ← receive sock r.stopped then
      if let some m := Mdns.decode bytes then
        if let some source := source then
          let port := match source with | .v4 a => a.port | .v6 a => a.port
          let isTail : Bool := match source with
            | .v4 a => Link.isTailnet (a.addr.octets.toList.map (·.toNat))
            | _ => false
          if let some (reply, unicast) := Mdns.response (if isTail then routed else offered) m port then
            send sock reply (if unicast then source else Mdns.Net.groupAddr)
        for f in (Mdns.found serviceType m).take 4 do
          if let some op := foundOp f now then
            let some (.discovered peer _ _ _) := (Codec.decode op.body : Option Community.Body) | continue
            if peer == me then continue
            let known : Answer F ← (Lists.list (Community.discoveryKnown.query [peer] (some 0) (cap := 1)) : SqlM F _).run db
            if known.total = 0 then continue
            let previous ← ((Discovery.latest Community.discovered.byPeer [peer]).run : SqlM F _).run db
            let recent : Bool := match previous with
              | some (.discovered _ _ time _) => now < time + 15000
              | _ => false
            unless recent do
              discard <| r.writes.trySend [op]
    -- Bound unsolicited multicast processing even if the link is flooded.
    IO.sleep 100

/-- The app starts this beside the TCP runner; both share its stop flag. -/
def start (r : Runner) (path : String) (tailnet : List IPv4Addr := []) : IO Unit := do
  discard <| IO.asTask (prio := .dedicated) do
    try
      let db ← Db.openAt path
      run r db tailnet
    catch e => IO.eprintln s!"discovery: {e}"

end Connection.DiscoveryNet
