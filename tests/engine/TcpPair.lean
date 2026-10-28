/-
Two nodes syncing a real community over real TCP on localhost, each
run by the engine's runner (`Runner`), with a toy handshake family in
place of the Connection family. The toy family exercises every path the
real one uses:

- a: writes a hello (a conn op naming b's address) and a courier for it
  locally; the outbox sends it bare to b, and the node purges the courier;
- b: takes the hello from the bare wire (`onFrame`, conn ops only),
  records its arrival and the address (`recv`), answers with an ack
  (`react`) and its courier, sent bare back on the same socket;
- both: list the session as established once the ack exists
  (`established`), so the node opens it and seals every frame after
  (a toy cipher naming its session, `sealFor`/`openFrame`).

Then the nodes sync a history to rest; a frame that does not open is
ignored; a dropped session is not reopened; the app hears every stored
id (`notify`).
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
  rooms := fun _ => pure rooms
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
    let adm := admit c req.id [ok.id]
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
  let dir := args.headD "out/tcppair"
  IO.FS.createDirAll dir
  let t ← Checks.new
  let (h, c) := history 4 40
  let x : Sync Fact (SqlM Fact) := { fam, cfg := { every := 5000, patience := 8000 }, hooks := hooks [c] }
  let pa := dir ++ "/a.db"
  let pb := dir ++ "/b.db"
  let da ← fresh pa
  let db ← fresh pb
  (receive fam (intake fam true h)).run da
  (receive fam (intake fam true (h.take 30))).run db
  let heard ← IO.mkRef (0 : Nat)
  let rb ← Runner.start x db 0 0 (fun ids => heard.modify (· + ids.length))
  let ra ← Runner.start x da 0 0
  let addrB := s!"127.0.0.1:{rb.port}".toUTF8
  -- a dials b: its hello names b's address.
  let hello := Op.make kHello [] addrB
  ra.write [hello, courier hello addrB]
  let mut done := false
  for _ in [0:400] do
    IO.sleep 50
    if (data (← idsAt pb) h).length == h.length then
      done := true
      break
  IO.eprintln s!"b holds {(data (← idsAt pb) h).length} of {h.length}"
  t.ok "tcp: b receives the whole history over TCP" done
  t.ok "tcp: b's app heard the stored ids" ((← heard.get) ≥ h.length - 30)
  -- a writes a post after the round: it streams to b.
  let late := post c c (Device.named "tcp-founder") "k".toUTF8 "late over tcp".toUTF8 1 999999
  ra.write [late]
  let mut streamed := false
  for _ in [0:100] do
    IO.sleep 50
    if (← idsAt pb).any (· == late.id) then
      streamed := true
      break
  t.ok "tcp: a new post streams to b" streamed
  ra.stop
  rb.stop
  -- A frame that does not open is ignored; the session stays.
  let dm ← Db.openAt ":memory:"
  let cid := sha256 "s".toUTF8
  let xs : Sync Fact (SqlM Fact) := { x with hooks := { x.hooks with
    established := pure [(cid, "10.0.0.7:1".toUTF8, true)] } }
  let run (n : Node) (f : Node → SqlM Fact (Node × Effects)) : IO (Node × Effects) := (f n).run dm
  let (n, _) ← run (Node.boot fam [] 0) fun n => n.onTick xs 1
  t.ok "session: an established session is opened" ((n.conn? cid).isSome)
  let (n, e) ← run n fun n => n.onFrame xs "10.0.0.7:1".toUTF8 (tagged sealedTag "tampered".toUTF8) 2
  t.ok "seal: a frame that does not open is ignored" (e.send.isEmpty && e.stored.isEmpty && (n.conn? cid).isSome)
  -- A session dropped here (patience) is not reopened, though the family
  -- still lists it.
  let (n, _) ← run (n.drop cid) fun n => n.onTick xs 3
  t.ok "session: a dropped session is not reopened" ((n.conn? cid).isNone && has n.dropped cid)
  -- A resent bare op is taken once: the family hears it again (`recv`)
  -- but its arrival record is the same op, and nothing new is stored.
  let hello := Op.make kHello [] "127.0.0.1:1".toUTF8
  let (n, e1) ← run n fun n => n.onFrame x "10.0.0.9:5".toUTF8 (tagged bareTag hello.bytes) 4
  let (_, e2) ← run n fun n => n.onFrame x "10.0.0.9:5".toUTF8 (tagged bareTag hello.bytes) 5
  let recs := (← (dumpOps (F := Fact)).run dm).filter (·.kind == kRecord)
  t.ok "bare: a resent op is taken once" (e1.stored.any (· == hello.id) && e2.stored.isEmpty && recs.length == 1)
  -- The family hears every arrival, a repeat included.
  let heardRecv ← IO.mkRef (0 : Nat)
  let xc : Sync Fact (SqlM Fact) := { x with hooks := { x.hooks with
    recv := fun c a o now => do
      heardRecv.modify (· + 1)
      x.hooks.recv c a o now } }
  let dc ← Db.openAt ":memory:"
  let (nc, _) ← (Node.boot fam [] 0 |>.onFrame xc "10.0.0.9:5".toUTF8 (tagged bareTag hello.bytes) 3).run dc
  let (_, _) ← (nc.onFrame xc "10.0.0.9:5".toUTF8 (tagged bareTag hello.bytes) 4).run dc
  t.ok "bare: the family hears a repeat arrival" ((← heardRecv.get) == 2)
  -- A stopped runner frees its port: start, stop and start again on it.
  let d1 ← fresh (dir ++ "/r1.db")
  let r1 ← Runner.start x d1 0 0
  let port := r1.port
  r1.stop
  let d2 ← fresh (dir ++ "/r2.db")
  let again ← (Runner.start x d2 0 port).toBaseIO
  match again with
  | .ok r2 =>
    t.ok "runner: a stopped runner's port takes a new runner" (r2.port == port)
    r2.stop
  | .error e => t.ok s!"runner: a stopped runner's port takes a new runner ({e})" false
  let code ← t.finish "tcppair"
  -- The listener and the readers never end by themselves: exit.
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
