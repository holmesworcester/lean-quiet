/-
A busy store never stops the runner (busy-retry, engine/core/Busy.lean),
over real TCP on localhost with two runners: the regression for
"network runner stopped: database is locked", which ended a node's sync
for good when a write waited on SQLite's lock past its busy timeout
(the long holder: a COMMIT's fsync under disk contention; status-9.md,
2026-11-01).

The deterministic case: a and b sync a history over TCP (tcppair's toy
handshake family); then a second connection to b's file takes SQLite's
write lock (`BEGIN IMMEDIATE`) and holds it for `hold` ms, past the
glue's 5 s busy timeout, while a writes a post that streams to b. b's
runner must still be running when the lock is released, and then store
the post. Run against the runner as it shipped (the store call run as
is: tests/engine/busy_runner_negative.sh), the runner stops with
"database is locked" and the post never arrives.

    busy_runner <outdir> [hold-ms]
-/
import tests.engine.Lib

open Engine Engine.Sync Community Tests

def C := ed25519
def base := family C

/-- The toy handshake's kinds: hello and ack cross the bare wire; the
arrival record and the courier are local. -/
def kHello : UInt8 := 250
def kRecord : UInt8 := 251
def kCourier : UInt8 := 252
def kAck : UInt8 := 253

def fam : Family Fact :=
  { base with scope := fun o =>
      if o.kind == kHello || o.kind == kAck then .conn
      else if o.kind == kRecord || o.kind == kCourier then .local
      else base.scope o }

/-- A courier: op x, to a bare address; the node purges it once sent. -/
def courier (x : Op) (addr : ByteArray) : Op := Op.make kCourier [x.id] addr

def opsOf (k : UInt8) : SqlM Fact (List Op) := do
  return (← dumpOps (F := Fact)).filter (·.kind == k)

/-- (hello, address it came from), from the arrival records. -/
def records : SqlM Fact (List (Id × ByteArray)) := do
  return (← opsOf kRecord).filterMap fun o => (Codec.decode o.body : Option (Id × ByteArray))

/-- A toy cipher: a frame names its session and carries the bytes
flipped; one that does not decode does not open. -/
def toySeal (cid : Id) (b : ByteArray) : SqlM Fact (Option ByteArray) :=
  pure (some (Codec.encode (cid, ByteArray.mk (b.data.map (· ^^^ 0xA5)))))

def toyOpen (f : ByteArray) : SqlM Fact (Option (Id × ByteArray)) :=
  pure ((Codec.decode f : Option (Id × ByteArray)).map fun (c, b) => (c, ByteArray.mk (b.data.map (· ^^^ 0xA5))))

def hooks (rooms : List Id) : Hooks Fact (SqlM Fact) where
  rooms := fun _ => pure (rooms.map .sync)
  recv := fun cid addr o _ => pure <|
    if cid.isNone && o.kind == kHello then [Op.make kRecord [] (Codec.encode (o.id, addr))] else []
  outbox := do
    let mut out := []
    for c in ← opsOf kCourier do
      if let some o ← Store.getOp (F := Fact) (c.reqs.headD .empty) then out := (c.id, c.body, o.bytes) :: out
    return out
  react := do
    let acks := (← opsOf kAck).map (·.reqs.headD .empty)
    return (← records).flatMap fun (h, addr) =>
      if acks.any (· == h) then [] else
      let a := Op.make kAck [h] "ack".toUTF8
      [a, courier a addr]
  established := do
    let recs ← records
    let acks := (← opsOf kAck).map (·.reqs.headD .empty)
    let answered := recs.filterMap fun (h, addr) => if acks.any (· == h) then some (h, addr, false) else none
    let dialed := (← opsOf kHello).filterMap fun h =>
      if !recs.any (·.1 == h.id) && acks.any (· == h.id) then some (h.id, h.body, true) else none
    return answered ++ dialed
  sealFor := toySeal
  openFrame := toyOpen

def history (members posts : Nat) : List Op × Id := Id.run do
  let f := Device.named "tcp-founder"
  let r := root f (keyOf f)
  let c := r.id
  let mut ops : Array Op := #[r]
  let mut adms : Array (Id × Device) := #[(c, f)]
  for j in [0:members] do
    let b := Device.named s!"tcp-bearer-{j}"
    let d := Device.named s!"tcp-member-{j}"
    let inv := invite c c f b.pk false
    let req := request c inv.id d (keyOf d) b.sk
    let ok := approve c req.id c f
    let adm := admit c req.id ok.id
    ops := ops ++ #[inv, req, ok, adm]
    adms := adms.push (adm.id, d)
  for i in [0:posts] do
    let (a, d) := adms[i % adms.size]!
    ops := ops.push (post c a d "k".toUTF8 s!"tcp post {i}".toUTF8 (i + 1) (1000 + 100 * i))
  return (ops.toList, c)

def fresh (path : String) : IO Db := do
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  Db.openAt path

def idsAt (path : String) : IO (List Id) := do
  return (← (dumpOps (F := Fact)).run (← Db.openAt path)).map (·.id)

def data (ids : List Id) (h : List Op) : List Id := ids.filter fun i => h.any (·.id == i)

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/busy_runner"
  let hold := (args[1]? >>= String.toNat?).getD 7000
  IO.FS.createDirAll dir
  let t ← Checks.new
  let (h, c) := history 2 20
  let x : Sync Fact (SqlM Fact) := { fam, cfg := { askTime := 8000 }, hooks := hooks [c] }
  let pa := dir ++ "/a.db"
  let pb := dir ++ "/b.db"
  let da ← fresh pa
  let db ← fresh pb
  (receive fam (intake fam true h)).run da
  (receive fam (intake fam true (h.take 10))).run db
  let rb ← Runner.start x db 0 0
  let ra ← Runner.start x da 0 0
  let addrB := s!"127.0.0.1:{rb.port}".toUTF8
  let hello := Op.make kHello [] addrB
  ra.write [hello, courier hello addrB]
  let mut synced := false
  for _ in [0:400] do
    IO.sleep 50
    if (data (← idsAt pb) h).length == h.length then
      synced := true
      break
  t.ok "busy: a and b sync over TCP first" synced
  -- Another connection holds b's write lock past the busy timeout while
  -- a's post streams to b.
  let lock ← Db.openAt pb
  lock.exec "BEGIN IMMEDIATE"
  let late := post c c (Device.named "tcp-founder") "k".toUTF8 "written while b is locked".toUTF8 1 999999
  ra.write [late]
  IO.sleep hold.toUInt32
  let aliveLocked := !(← IO.hasFinished rb.done)
  let heldOut := !(← idsAt pa).isEmpty && !((← (dumpOps (F := Fact)).run lock).any (·.id == late.id))
  lock.exec "COMMIT"
  t.ok s!"busy: b's runner is still running after {hold} ms of a held write lock (past the 5 s busy timeout)" aliveLocked
  t.ok "busy: the post was not stored while the lock was held" heldOut
  let mut stored := false
  for _ in [0:200] do
    IO.sleep 50
    if (← idsAt pb).any (· == late.id) then
      stored := true
      break
  t.ok "busy: after the release, b stores the post" stored
  t.ok "busy: and b's runner is still running" (!(← IO.hasFinished rb.done))
  -- and sync goes on: another post after the release streams too
  let after := post c c (Device.named "tcp-founder") "k".toUTF8 "after the release".toUTF8 2 1000000
  ra.write [after]
  let mut streamed := false
  for _ in [0:200] do
    IO.sleep 50
    if (← idsAt pb).any (· == after.id) then
      streamed := true
      break
  t.ok "busy: a later post streams to b as before" streamed
  ra.stop
  rb.stop
  let code ← t.finish "busy_runner"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
