/-
Two nodes syncing a real community over real TCP on localhost, each
run by the engine's runner (`Runner`), with a toy handshake family in
place of the Connection family. The toy family exercises every path the
real one uses:

- a: writes a hello (a conn op naming b's address) locally; the outbox
  sends it bare to b and marks it shipped;
- b: takes the hello from the bare wire (`onBare`, conn ops only),
  records its arrival and the address (`recv`), answers with an ack
  (`react`), sent bare back on the same socket;
- both: list the session as established once the ack exists
  (`established`), so the node opens it, binds the socket (`bind`) and
  seals every frame after (a counter-checked toy cipher, `session`).

Then the nodes sync a 101-op history to rest; a frame that does not
unseal drops the session; the app hears every stored id (`notify`).
-/
import Tests.Lib

open Engine Engine.Sync Community Tests

def C := ed25519
def base := family C

/-- The toy handshake's kinds: hello and ack cross the bare wire; the
arrival record and the shipped marker are local. -/
def kHello : UInt8 := 250
def kRecord : UInt8 := 251
def kShipped : UInt8 := 252
def kAck : UInt8 := 253

def fam : Family Fact :=
  { base with scope := fun o =>
      if o.kind == kHello || o.kind == kAck then .conn
      else if o.kind == kRecord || o.kind == kShipped then .local
      else base.scope o }

def opsOf (k : UInt8) : SqlM Fact (List Op) := do
  return (← dumpOps (F := Fact)).filter (·.kind == k)

/-- (hello, address it came from), from the arrival records. -/
def records : SqlM Fact (List (Id × ByteArray)) := do
  return (← opsOf kRecord).filterMap fun o => (Codec.decode o.body : Option (Id × ByteArray))

/-- A toy cipher whose state is the two counters: a frame is its
counter, then the payload with every byte flipped; a frame whose counter
is not the next one does not open. -/
def toySealer : Sealer where
  state := Codec.encode ((0 : Nat), (0 : Nat))
  sealFrame st p :=
    let (s, r) := (Codec.decode st : Option (Nat × Nat)).getD (0, 0)
    (Codec.encode (s + 1, r), Codec.encode (s, ByteArray.mk (p.data.map (· ^^^ 0xA5))))
  openFrame st f := do
    let (s, r) ← (Codec.decode st : Option (Nat × Nat))
    let (n, body) ← (Codec.decode f : Option (Nat × ByteArray))
    if n != r then none
    else some (Codec.encode (s, r + 1), ByteArray.mk (body.data.map (· ^^^ 0xA5)))

def hooks (rooms : List Id) : Hooks Fact where
  rooms := fun _ => pure rooms
  recv := fun cid addr o _ =>
    if cid.isNone && o.kind == kHello then [Op.make kRecord [] (Codec.encode (o.id, addr))] else []
  outbox := do
    let shipped := (← opsOf kShipped).map (·.body)
    let recs ← records
    let mine := (← opsOf kHello).filter fun h => !recs.any (·.1 == h.id)
    let hellos := mine.filterMap fun h =>
      if shipped.any (· == h.id) then none else some (h.id, Route.bare h.body, h.bytes)
    let acks := (← opsOf kAck).filterMap fun a =>
      if shipped.any (· == a.id) then none else
      match a.reqs, recs.find? (·.1 == a.reqs.headD .empty) with
      | [_], some (_, addr) => some (a.id, Route.bare addr, a.bytes)
      | _, _ => none
    return hellos ++ acks
  shipped := fun i => [Op.make kShipped [] i]
  react := do
    let acks := (← opsOf kAck).map (·.reqs.headD .empty)
    return (← records).filterMap fun (h, _) =>
      if acks.any (· == h) then none else some (Op.make kAck [h] "ack".toUTF8)
  established := do
    let recs ← records
    let acks := (← opsOf kAck).map (·.reqs.headD .empty)
    let answered := recs.filterMap fun (h, addr) => if acks.any (· == h) then some (h, addr, false) else none
    let dialed := (← opsOf kHello).filterMap fun h =>
      if !recs.any (·.1 == h.id) && acks.any (· == h.id) then some (h.id, h.body, true) else none
    return answered ++ dialed
  session := fun _ => pure (some toySealer)

def history (members posts : Nat) : List Op × Id := Id.run do
  let f := Device.named "tcp-founder"
  let r := root f
  let c := r.id
  let mut ops : Array Op := #[r]
  let mut adms : Array (Id × Device) := #[(c, f)]
  for j in [0:members] do
    let b := Device.named s!"tcp-bearer-{j}"
    let d := Device.named s!"tcp-member-{j}"
    let inv := invite c c f b.pk false
    let req := request c inv.id d b.sk
    let ok := approve c req.id c f
    let adm := admit c req.id [ok.id]
    ops := ops ++ #[inv, req, ok, adm]
    adms := adms.push (adm.id, d)
  for i in [0:posts] do
    let (a, d) := adms[i % adms.size]!
    ops := ops.push (post c a d "k".toUTF8 s!"tcp post {i}".toUTF8 (1000 + 100 * i))
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
  let x : Sync Fact := { fam, cfg := { every := 5000, patience := 8000 }, hooks := hooks [c] }
  let pa := dir ++ "/a.db"
  let pb := dir ++ "/b.db"
  let da ← fresh pa
  let db ← fresh pb
  (receive fam (intake fam true h)).run da
  (receive fam (intake fam true (h.take 30))).run db
  let heard ← IO.mkRef (0 : Nat)
  let rb ← Runner.start x (← Node.boot x db 0) 0 (fun ids => heard.modify (· + ids.length))
  let ra ← Runner.start x (← Node.boot x da 0) 0
  let addrB := s!"127.0.0.1:{rb.port}".toUTF8
  -- a dials b: its hello names b's address.
  ra.write [Op.make kHello [] addrB]
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
  let late := post c c (Device.named "tcp-founder") "k".toUTF8 "late over tcp".toUTF8 999999
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
  -- A session frame that does not unseal drops the session (on a node
  -- with a session open, in memory).
  let dm ← Db.openAt ":memory:"
  let n ← Node.boot x dm 0
  let cid := sha256 "s".toUTF8
  let (n, _) ← n.open x cid true toySealer 0
  let (n, e) ← n.onBytes x cid "tampered".toUTF8 1
  t.ok "seal: a frame that does not unseal drops the session" (e.drop.any (· == cid) && (n.conn? cid).isNone)
  let (n, _) ← n.onTick x 2
  t.ok "seal: a dropped session is not reopened" ((n.conn? cid).isNone && has n.dropped cid)
  let code ← t.finish "tcppair"
  -- The listener and the readers never end by themselves: exit.
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
