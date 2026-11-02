/- The actual Runner/SQLite/Node/socket writer under sustained wanted-data
pressure. A raw TCP peer deliberately loses control payloads and two target
copies, but feeds delivered data through the actual receiver Node. Plain
session sealing isolates transport admission; JoinFair retains Noise coverage. -/
import tests.engine.Lib
import engine.wire.Tcp
import engine.core.Exit

namespace ReservedRetry
open Engine Engine.Sync Community Tests Std.Async Std.Net

def fam : Family Fact := family ed25519
def author := Device.named "reserved-retry-author"
def rootOp := root author (keyOf author)
def message (n : Nat) := post rootOp.id rootOp.id author "catalog".toUTF8
  s!"retained message {n}".toUTF8 n (1000 + n)
def cid := sha256 "reserved-retry-session".toUTF8
def peerKey := "reserved-authenticated-peer".toUTF8

def setup (address : ByteArray) (established : Bool) : Sync Fact (SqlM Fact) :=
  { fam, cfg := { live := 1000000000, every := 1 },
    hooks := {
      rooms := fun _ => pure [.sync rootOp.id]
      sealFor := plainSeal
      openFrame := plainOpen
      retryKey := fun _ => pure (some peerKey)
      established := pure (if established then [(cid, address, true)] else []) },
    catalog := some Catalog.sql, retryStore := some RetryStore.sql }

def payloads (bytes : ByteArray) : List Op :=
  if bytes[0]? != some sealedTag then [] else
  match (Codec.decode (bytes.extract 1 bytes.size) : Option (Id × ByteArray)) with
  | none => []
  | some (_, inner) => ((Codec.decode inner : Option (List ByteArray)).getD []).filterMap Op.decode

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 10
  return false

def accept (srv : TCP.Socket.Server) : IO TCP.Socket.Client := do
  for _ in [0:500] do
    if let some c ← srv.tryAccept then return c
    IO.sleep 10
  throw (IO.userError "reserved retry fixture did not connect")

def ticketChecks (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  (receive fam [rootOp, message 1]).run db
  let x := { setup "peer".toUTF8 false with
    deferredRetries := true, retryRoom := fun _ => some maxFrame }
  let (n, _) ← ((Node.boot fam [rootOp, message 1] 0).connect x cid "peer".toUTF8 true 0).run db
  let store : RetryStore (SqlM Fact) := RetryStore.sql
  let before : Sweep := ⟨1, 2, true⟩
  (store.save peerKey before).run db
  let (n, acts) ← (n.sweep x cid).run db
  let (_, effects) ← (n.finish x acts 1).run db
  let current ← (store.load peerKey).run db
  t.ok "prepared retry does not advance durable cursor before native write"
    (decide (current = before) && effects.retry.length == 1 && !effects.send.isEmpty)
  let ticket := effects.retry.head!
  let (_, _) ← (n.onClose x "peer".toUTF8 2).run db
  t.ok "closing before writer completion preserves retry position"
    (decide ((← (store.load peerKey).run db) = before))
  (store.commit ticket).run db
  t.ok "writer completion ticket commits its exact next cursor"
    (decide ((← (store.load peerKey).run db) = ticket.after))
  let later : Sweep := ⟨4, 9, true⟩
  (store.save peerKey later).run db
  (store.commit ticket).run db
  t.ok "late completion from an old socket cannot rewind newer progress"
    (decide ((← (store.load peerKey).run db) = later))

def runnerChecks (t : Checks) : IO Unit := do
  let source ← Db.openAt ":memory:"
  let receiver ← Db.openAt ":memory:"
  let original := rootOp :: (List.range 8).map message
  (receive fam original).run source
  let target := message 7
  let large := (List.range 17).map fun i =>
    post rootOp.id rootOp.id author "catalog".toUTF8
      (ByteArray.mk (Array.replicate 1000000 (65 + i).toUInt8)) (200 + i) (2200 + i)
  t.ok "seventeen hot replies individually fit frames but exceed old atomic cap"
    (large.all (fun o => Sweep.cost o ≤ maxFrame) &&
      16777216 < (large.map (·.bytes.size)).sum)
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  srv.listen 1
  let remote := (addrText (← srv.getSockName)).toUTF8
  let hotReady ← IO.mkRef false
  let lastId := large.getLast!.id
  let notify := fun ids : List Id => if ids.contains lastId then hotReady.modify (fun _ => true) else pure ()
  -- No ordinary serving window. Each wanted hot payload also exceeds the
  -- normal queue cap, so recovery must use its independent reservation.
  let cfg : RunConfig := {
    tickMs := 20, window := 0, sockCap := 262144
    stallMs := 5000, idle := 1000000000 }
  let run ← Runner.start (setup remote true) source 0 0 notify cfg
  let client ← accept srv
  let aborter ← SocketAbort.capture client
  run.write large
  t.ok "actual runner commits the large hot batch" (← waitFor 5000 hotReady.get)
  let peerStop ← StopFlag.new
  let posting ← IO.mkRef true
  let readTarget ← IO.mkRef false
  let copies ← IO.mkRef 0
  let wanted ← IO.mkRef 0
  let posted ← IO.mkRef 0
  let offered := tagged sealedTag (Codec.encode (cid, Codec.encode [(Msg.want (large.map Op.id)).op.bytes]))
  let flood ← IO.asTask (prio := .dedicated) do
    while !(← peerStop.get) do
      unless ← SocketAbort.awaitSend aborter 2000 peerStop.get (client.native.send #[frame offered]) do break
      wanted.modify (· + 1)
      IO.sleep 10
  let producer ← IO.asTask (prio := .dedicated) do
    let mut i := 0
    while ← posting.get do
      if ← run.writes.trySend [message (1000 + i)] then
        i := i + 1
        posted.modify (fun _ => i)
      IO.sleep 40
  let received ← IO.asTask (prio := .dedicated) do
    let y := setup "source".toUTF8 false
    let (initial, _) ← ((Node.boot fam [] 0).connect y cid "source".toUTF8 false 0).run receiver
    let mut node := initial
    let mut buf := ByteArray.empty
    -- Force queued and in-flight pressure before letting the peer drain.
    IO.sleep 350
    while !(← peerStop.get) do
      let some chunk ← readSocket client peerStop 65536 | break
      let (frames, kept) := Engine.Sync.frames (buf ++ chunk)
      buf := kept.getD .empty
      for payload in frames do
        let ops := payloads payload
        let isTarget := ops.any (·.id == target.id)
        if isTarget then copies.modify (· + 1)
        if ops.any (fun o => !isWire o.kind) && (!isTarget || 2 < (← copies.get)) then
          let (next, _) ← (node.onFrame y "source".toUTF8 payload (← IO.monoMsNow)).run receiver
          node := next
          if (← (Store.getOp target.id : SqlM Fact _).run receiver) == some target then
            readTarget.modify (fun _ => true)
  let began ← IO.monoMsNow
  let arrived ← waitFor 20000 readTarget.get
  let elapsed := (← IO.monoMsNow) - began
  IO.println s!"reserved TCP recovery: {elapsed} ms; target copies {← copies.get}; wanted batches {← wanted.get}; new posts {← posted.get}"
  t.ok "reserved retry crosses actual TCP despite continuously refused normal data" arrived
  t.ok "lost target receives at least three actual native wire attempts" ((← copies.get) ≥ 3)
  t.ok "ordinary wants and new posting continue until target delivery"
    ((← wanted.get) ≥ 20 && (← posted.get) ≥ 10 && !(← IO.hasFinished flood) && !(← IO.hasFinished producer))
  t.ok "actual loop services flooded peer frames during retry recovery"
    ((← run.counters).events.toNat ≥ 20)
  posting.modify (fun _ => false)
  peerStop.request
  if let some cap := aborter then discard <| cap.abort
  for task in [producer, flood, received] do
    if let .error e ← IO.wait task then throw e
  -- SQLite THREADSAFE=2 requires one owner per connection. Stop the loop
  -- before inspecting its connection from this observer thread.
  run.stop
  let targetStatus ← (Store.getStatus target.id : SqlM Fact _).run receiver
  t.ok "received target settles to the same valid view input"
    (targetStatus == (← (Store.getStatus target.id : SqlM Fact _).run source) &&
      targetStatus.any (fun v => match v with | .valid _ => true | _ => false))
  let progress ← ((RetryStore.sql (F := Fact)).load peerKey).run source
  t.ok "actual completed writer attempts persist peer retry progress" (progress.after > 0)
  closeListener srv.native

end ReservedRetry

def mainBody : IO UInt32 := do
  let t ← Tests.Checks.new
  ReservedRetry.ticketChecks t
  ReservedRetry.runnerChecks t
  t.finish "reserved-retry"

/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main : IO UInt32 := Engine.exitAfter mainBody
