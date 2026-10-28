/-
Daybreak regressions against the actual Conn, Node and SQLite purge
path. The instrumented Store records blob reads; the memory transport
carries real node frames and ends sessions with Node.onClose.
-/
import tests.engine.Checks
import engine.wire.Tcp

open Engine Engine.Sync Tests
namespace Harden

instance : SortKey Nat := ⟨fun _ => .empty⟩

def fam : Family Nat :=
  { validate := fun _ _ => some 0, keys := fun _ => [],
    scope := fun o => if o.kind == 1 then .shared (o.reqs.headD .empty) else .local }

def session := Op.make 240 [] "harden-session".toUTF8
def key1 := Op.make 241 [session.id] "send-key-0123456789abcdef".toUTF8
def key2 := Op.make 242 [session.id] "recv-key-fedcba9876543210".toUTF8

def seed (db : Db) : IO Unit := (Turn.turn fam [session, key1, key2] : SqlM Nat Unit).run db

def keysGone (db : Db) : IO Bool := do
  let ops ← (dumpOps (F := Nat)).run db
  return !ops.any (fun o => o.id == key1.id || o.id == key2.id || o.id == session.id)

def setup (addr : ByteArray) (dialer : Bool) (cfg : Config := {}) : Sync Nat (SqlM Nat) :=
  { fam, cfg, hooks := {
      rooms := fun _ => pure [.sync "room".toUTF8]
      closing := fun _ => pure [session.id]
      established := do
        if (← Store.getOp (F := Nat) session.id).isSome then return [(session.id, addr, dialer)]
        return []
      sealFor := plainSeal, openFrame := plainOpen } }

structure Trace where
  ops : List Op := []
  reads : List Id := []

abbrev TM := StateM Trace

instance : Store Nat TM where
  getOp i := do
    modify fun s => { s with reads := s.reads ++ [i] }
    return (← get).ops.find? (·.id == i)
  putOp _ := pure ()
  getStatus _ := pure none
  setStatus _ _ := pure ()
  addWait _ _ := pure ()
  waiters _ := pure []
  clearWaiters _ := pure ()
  push _ := pure ()
  pop := pure none
  index _ _ := pure ()
  lookup _ := pure []

def clockChecks (t : Checks) : IO Unit := do
  let cfg : Config := { every := 30, patience := 20, lease := 90 }
  let c : Conn := { dialer := true, rooms := ["room".toUTF8], floor := 0, peerFloor := some 0, heard := 1 }
  let started := c.start cfg {} 1000
  for now in [1000:1021] do
    let s := ((started.conn.tick fam cfg {} now : TM Step).run {}).1
    t.ok s!"new round survives tick {now}" (!s.drop)
  t.ok "round drops strictly after patience" (((started.conn.tick fam cfg {} 1021 : TM Step).run {}).1.drop)
  let responder := { c with dialer := false, heard := 1000 }
  t.ok "unwaiting responder expires" (((responder.tick fam cfg {} 1091 : TM Step).run {}).1.drop)
  for now in [1000:1031] do
    t.ok s!"cadence keeps lease at {now}" (!responder.expired cfg now)
  let r := "room".toUTF8
  let s := responder.onRbsr cfg {} r 7 [.ids ⟨⟨0, 0⟩, none⟩ []] 1001
  t.ok "uncarried shown room is answered" (!s.send.isEmpty)

def wantChecks (t : Checks) : IO Unit := do
  let a := "removed-room-A".toUTF8
  let b := "live-room-B".toUTF8
  let x := Op.make 1 [a] ⟨Array.replicate (1024 * 1024) 42⟩
  let y := Op.make 1 [b] "small".toUTF8
  let z := Op.make 1 [b] "next".toUTF8
  let c : Conn := { dialer := false, rooms := [b], floor := 0 }
  let ix := Index.ofOps fam [x, y, z]
  let (s, trace) := (c.onWant fam {} ix [x.id, y.id] : TM Step).run { ops := [x, y, z] }
  t.ok "cross-room want sends only y" (s.send.map (·.id) == [y.id])
  t.ok "cross-room want never reads large x" (trace.reads == [y.id])
  let (s2, trace2) := (c.onWant fam {} ix [x.id, y.id] : TM Step).run { ops := [y, z] }
  t.ok "outside possession changes neither reads nor reply" (trace2.reads == trace.reads && s2.send.map (·.id) == s.send.map (·.id))
  let cfg : Config := { wantBytes := y.bytes.size }
  let (s, trace) := (c.onWant fam cfg ix [y.id, z.id] : TM Step).run { ops := [x, y, z] }
  t.ok "budget stops subsequent blob reads" (trace.reads == [y.id] && s.send.map (·.id) == [y.id])
  let (s, trace) := (c.onWant fam { wantBytes := 0 } ix [y.id] : TM Step).run { ops := [y] }
  t.ok "zero budget reads and sends nothing" (trace.reads.isEmpty && s.send.isEmpty)
  let (s, trace) := (c.onWant fam { wantBytes := 1 } ix [y.id, z.id] : TM Step).run { ops := [y,z] }
  t.ok "one oversize op is whole; next is unread" (trace.reads == [y.id] && s.send.map (·.id) == [y.id])

def memoryChecks (t : Checks) : IO Unit := do
  let da ← Db.openAt ":memory:"
  let db ← Db.openAt ":memory:"
  seed da; seed db
  let a := "a".toUTF8
  let b := "b".toUTF8
  let xa := setup b true
  let xb := setup a false
  let (na, ea) ← ((Node.boot fam [] 0).onTick xa 0).run da
  let (nb, eb) ← ((Node.boot fam [] 0).onTick xb 0).run db
  let mut na := na
  let mut nb := nb
  for (_, bytes) in ea.send do nb := (← (nb.onFrame xb a bytes 1).run db).1
  for (_, bytes) in eb.send do na := (← (na.onFrame xa b bytes 1).run da).1
  t.ok "two nodes exchange session hellos in memory" ((na.conn? session.id).any (·.peerFloor.isSome) && (nb.conn? session.id).any (·.peerFloor.isSome))
  t.ok "both stores hold both keys before close" (!(← keysGone da) && !(← keysGone db))
  na := (← (na.onClose xa b 2).run da).1
  let (nbClosed, e) ← (nb.onClose xb a 2).run db
  t.ok "transport end closes responder and reports drop" ((nbClosed.conn? session.id).isNone && e.drop == [session.id])
  t.ok "transport end purges both stores' session keys" ((← keysGone da) && (← keysGone db))
  na := (← (na.onTick xa 3).run da).1
  t.ok "closed session never reopens" ((na.conn? session.id).isNone)
  for reason in [0:3] do
    let d ← Db.openAt ":memory:"
    seed d
    let x := setup a (reason == 0) { patience := 2, lease := 3 }
    let (n, _) ← ((Node.boot fam [] 0).onTick x 0).run d
    let n := if reason == 1 then { n with conns := n.conns.map fun (id,c) => (id,{c with peerFloor := some 0}) } else n
    let x := if reason == 2 then { x with hooks := { x.hooks with retired := pure [session.id] } } else x
    let (n, e) ← (n.onTick x (if reason == 2 then 1 else 4)).run d
    t.ok s!"end path {reason} removes connection and keys" ((n.conn? session.id).isNone && e.drop.contains session.id && (← keysGone d))

/-- Count actual wanted ids on the wire, including all retry chunks. -/
def wanted (ops : List Op) : List Id := ops.flatMap fun o =>
  match Msg.ofOp o with | some (.want ids) => ids | _ => []

def hostileChecks (t : Checks) : IO Unit := do
  let d ← Db.openAt ":memory:"
  seed d
  let cfg : Config := { maxKnown := 16, maxIds := 4, patience := 20, retry := 1 }
  let x := setup "hostile".toUTF8 false cfg
  let (n, _) ← ((Node.boot fam [] 0).onTick x 0).run d
  let mut n := n
  let mut peak := 0
  let mut bounded := true
  let mut drops := 0
  let mut retriesBounded := true
  for i in [1:1001] do
    let bytes := tagged sealedTag (Codec.encode (session.id, Codec.encode [(Msg.hold "room".toUTF8 [sha256 s!"fresh-{i}".toUTF8]).op.bytes]))
    let (next, e) ← (n.onFrame x "hostile".toUTF8 bytes i).run d
    n := next
    drops := drops + e.drop.length
    if let some c := n.conn? session.id then
      peak := max peak (max c.known.size c.asked.size)
      bounded := bounded && c.known.size ≤ cfg.maxKnown && c.asked.size ≤ cfg.maxKnown && c.askTime.size ≤ cfg.maxKnown
      let tick ← (c.tick fam cfg {} i : SqlM Nat Step).run d
      retriesBounded := retriesBounded && (wanted tick.send).length ≤ cfg.maxIds
    let (next, e) ← (n.onTick x i).run d
    n := next
    drops := drops + e.drop.length
  t.ok "1000 fresh holds bound sets and timestamps" (bounded && peak == cfg.maxKnown)
  t.ok "fresh holds never drop for set size" (drops == 0 && (n.conn? session.id).isSome && !(← keysGone d))
  t.ok "hostile retries bounded per tick" retriesBounded
  let c : Conn := { dialer := false, rooms := ["room".toUTF8], floor := 0, peerFloor := some 0 }
  let (s, tr) := (c.onHold fam { maxIds := 1 } "room".toUTF8 ["x".toUTF8,"y".toUTF8] : TM Step).run {}
  t.ok "oversized hold ignored before any read" (!s.drop && tr.reads.isEmpty && s.send.isEmpty)
  let ids := (List.range 5).map fun i => s!"pending-{i}".toUTF8
  let cfg : Config := { maxKnown := 4, maxIds := 5, patience := 20, retry := 1 }
  let first := (({ c with heard := 10 }.onHold fam cfg "room".toUTF8 ids : TM Step).run {}).1
  t.ok "full asked defers missing ids without remembering them" (first.conn.asked.size == 4 && first.conn.known.size == 4 && !first.conn.known.contains ids[4]! && (wanted first.send) == ids.take 4)
  let again := (({ first.conn with heard := 20 }.onHold fam cfg "room".toUTF8 ids : TM Step).run {}).1
  t.ok "repeat offers do not renew original ask times" (again.conn.askTime[ids[0]!]? == some 10)
  let cfg := { cfg with maxIds := 2 }
  let retry := (({ again.conn with heard := 30 }.tick fam cfg {} 30 : TM Step).run {}).1
  t.ok "tick reasks at most maxIds before expiry" ((wanted retry.send).length == 2 && retry.conn.asked.size == 4)
  t.ok "retries do not renew original ask times" (retry.conn.askTime[ids[0]!]? == some 10)
  let expired := (({ retry.conn with heard := 31 }.tick fam cfg {} 31 : TM Step).run {}).1
  t.ok "asks expire after patience despite live peer traffic" (!expired.drop && expired.conn.asked.isEmpty && expired.conn.askTime.isEmpty && (wanted expired.send).isEmpty)
  let fresh := "fresh".toUTF8
  let old := "old".toUTF8
  let hints := remember 1 (({} : Std.HashSet Id).insert old) fresh
  t.ok "full known forgets old hints and remembers the new id" (hints.size == 1 && hints.contains fresh && !hints.contains old)
  t.ok "zero cap retains no hints or asks" ((remember 0 hints fresh).isEmpty && (admitAsks 0 {} ids).isEmpty)

def closeEffectsChecks (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  seed db
  let courier := Op.make 243 [] "courier".toUTF8
  (Turn.turn fam [courier] : SqlM Nat Unit).run db
  let addr := "not-an-address".toUTF8
  let x := setup "peer".toUTF8 false
  let x := { x with hooks := { x.hooks with outbox := do
    if (← Store.getOp (F := Nat) courier.id).isSome then
      return [(courier.id, addr, (Msg.hello 0).op.bytes)]
    return [] } }
  let n : Node := {
    ix := {}, floor := 0
    conns := [(session.id, (Conn.open false [] 0 0).conn)],
    addrs := [(session.id, "peer".toUTF8)], managed := [session.id] }
  let (n, e) ← (n.onClose x "peer".toUTF8 1).run db
  let slots : Slots ← Std.Mutex.new []
  let ch ← eventChannel { queue := 2 }
  let st : RunState := { db, node := n, slots }
  let st ← RunState.finishClose x ch (fun _ => pure ()) {} (st, e) 1
  t.ok "close effects retain a shipped courier for transport" (st.pending.any (·.1 == addr))
  let mut dialed := false
  for _ in [0:100] do
    if let some (.dialed a none) ← ch.tryRecv then
      dialed := a == addr
      break
    IO.sleep 1
  t.ok "close effects reach the transport's dial path" dialed
  t.ok "close effects still purge session keys" (← keysGone db)


def queueChecks (t : Checks) : IO Unit := do
  let ch ← eventChannel { queue := 1 }
  discard <| enqueue ch (.frame 1 .empty)
  let sent ← IO.mkRef false
  let task ← IO.asTask (prio := .dedicated) do
    discard <| enqueue ch (.frame 2 .empty)
    sent.set true
  IO.sleep 30
  t.ok "full queue blocks producer" (!(← sent.get))
  t.ok "first queued event retained" (match ← ch.tryRecv with | some (.frame 1 _) => true | _ => false)
  discard <| IO.wait task
  t.ok "blocked frame delivered after space" ((match ← ch.tryRecv with | some (.frame 2 _) => true | _ => false) && (← sent.get))
  let slots : Slots ← Std.Mutex.new []
  let cfg : RunConfig := { maxSocks := 3, perAddr := 2 }
  t.ok "first socket admitted" (← slots.take cfg "127.0.0.1:1".toUTF8)
  t.ok "second socket admitted" (← slots.take cfg "127.0.0.1:2".toUTF8)
  t.ok "source ports cannot evade per-address cap" (!(← slots.take cfg "127.0.0.1:3".toUTF8))
  t.ok "different peer can fill last slot" (← slots.take cfg "127.0.0.2:1".toUTF8)
  t.ok "global socket cap rejects more peers" (!(← slots.take cfg "127.0.0.3:1".toUTF8))
  slots.release "127.0.0.1:1".toUTF8
  t.ok "close releases exactly one slot" (← slots.take cfg "127.0.0.3:1".toUTF8)

end Harden
