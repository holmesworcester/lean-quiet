/- Actual Node handlers and SQLite, with signed community operations. The
transport drops every control frame and the first two copies of one target;
new signed posts arrive on every tick. This isolates durable data retries
from the RBSR/asked/owed optimizations. TCP/handshake coverage is JoinFair. -/
import tests.engine.Lib
import tests.engine.SqliteOpen
import engine.wire.Node

open Engine Engine.Sync Community Tests

namespace CatalogRetry

def fam : Family Fact := family ed25519
def author := Device.named "catalog-retry-author"
def rootOp := root author (keyOf author)
def message (n : Nat) := post rootOp.id rootOp.id author "catalog".toUTF8
  s!"retained message {n}".toUTF8 n (1000 + n)
def cid := sha256 "catalog-retry-session".toUTF8

def setup (authorized : Bool := true) : Sync Fact (SqlM Fact) :=
  { fam, cfg := { live := 1000000000, safety := 1000000000, maxKnown := 1, maxIds := 1 },
    hooks := {
      rooms := fun _ => pure (if authorized then [.sync rootOp.id] else [])
      sealFor := plainSeal
      openFrame := plainOpen
      retryKey := fun _ => pure (some "authenticated-test-peer".toUTF8) },
    catalog := some Catalog.sql, retryStore := some RetryStore.sql }

def payloads (bytes : ByteArray) : List Op :=
  if bytes[0]? != some sealedTag then [] else
  match (Codec.decode (bytes.extract 1 bytes.size) : Option (Id × ByteArray)) with
  | none => []
  | some (_, inner) => ((Codec.decode inner : Option (List ByteArray)).getD []).filterMap Op.decode

def hasOp (db : Db) (o : Op) : IO Bool := do
  return (← (Store.getOp o.id : SqlM Fact _).run db) == some o

def schemaChecks (ck : Checks) : IO Unit := do
  let db ← Db.open ":memory:"
  db.exec "CREATE TABLE ops (id BLOB PRIMARY KEY, bytes BLOB NOT NULL) WITHOUT ROWID"
  let _ ← db.query "INSERT INTO ops (id, bytes) VALUES (?, ?)" #[rootOp.id, rootOp.bytes]
  db.exec schema
  let initial ← (Catalog.sql (F := Fact)).ceiling.run db
  ck.ok "legacy database migration catalogs existing op" (initial == 1 &&
    (← ((Catalog.sql (F := Fact)).read 1).run db) == some rootOp.id)
  db.exec schema
  ck.ok "reopening schema neither appends duplicates nor advances high water"
    ((← (Catalog.sql (F := Fact)).ceiling.run db) == initial)
  let secretOp := Community.secret (sha256 "catalog local secret".toUTF8)
  (Store.putOp secretOp : SqlM Fact Unit).run db
  let localSeq ← (Catalog.sql (F := Fact)).ceiling.run db
  (purgeSql fam [secretOp.id] false).run db
  ck.ok "purge removes catalog id while preserving high water"
    ((← ((Catalog.sql (F := Fact)).read localSeq).run db).isNone &&
      (← (Catalog.sql (F := Fact)).ceiling.run db) == localSeq)
  (Store.putOp (message 1) : SqlM Fact Unit).run db
  ck.ok "next inserted op receives a new position after a purge"
    ((← (Catalog.sql (F := Fact)).ceiling.run db) == localSeq + 1 &&
      (← ((Catalog.sql (F := Fact)).read (localSeq + 1)).run db) == some (message 1).id)
  let plan ← db.query "EXPLAIN QUERY PLAN SELECT id FROM catalog WHERE seq = 1" #[]
  let planText := String.intercalate " " (plan.toList.flatMap fun row => row.toList.filterMap String.fromUTF8?)
  ck.ok "catalog lookup uses integer primary key, not a catalog scan"
    ((planText.splitOn "INTEGER PRIMARY KEY").length > 1)

def retryChecks (ck : Checks) : IO Unit := do
  let source ← Db.openAt ":memory:"
  let receiver ← Db.openAt ":memory:"
  let original := rootOp :: (List.range 8).map message
  (receive fam original).run source
  let x := setup
  let a0 := Node.boot fam original 0
  let b0 := Node.boot fam [] 0
  let (a0, _) ← (a0.connect x cid "receiver".toUTF8 true 0).run source
  let (b0, hello) ← (b0.connect x cid "source".toUTF8 false 0).run receiver
  let mut a := a0
  let mut b := b0
  let mut session := cid
  let mut opening := 0
  for (_, frame) in hello.send do
    let (next, out) ← (a.onFrame x "receiver".toUTF8 frame 0).run source
    a := next
    opening := opening + out.send.length
  ck.ok "real opening was emitted then lost, leaving its round active"
    (opening > 0 && (a.conn? cid).any (! ·.active.isEmpty))
  let target := message 7
  let mut targetCopies := 0
  let mut progressedWhileWriting := false
  let mut largestEmission := 0
  let mut reconnects := 0
  for tick in [1:260] do
    if tick % 3 == 0 then
      -- A session lasts fewer ticks than the initial target's catalog rank.
      -- Progress must survive these disposable session ids.
      let (next, _) ← (a.onClose x "receiver".toUTF8 tick).run source
      a := next
      let (next, _) ← (b.onClose x "source".toUTF8 tick).run receiver
      b := next
      session := sha256 s!"catalog-reconnect-{tick}".toUTF8
      let (next, _) ← (a.connect x session "receiver".toUTF8 true tick).run source
      a := next
      let (next, _) ← (b.connect x session "source".toUTF8 false tick).run receiver
      b := next
      reconnects := reconnects + 1
    -- The offers produced by these writes are all lost.
    let (next, _) ← (a.onWrite x [message (1000 + tick)] tick).run source
    a := next
    let (next, out) ← (a.onTick x tick).run source
    a := next
    let data := out.send.flatMap fun (_, frame) => (payloads frame).filter fun o => !isWire o.kind
    largestEmission := max largestEmission data.length
    for (_, frame) in out.send do
      let ops := payloads frame
      if ops.any (fun o => o.id == target.id) then targetCopies := targetCopies + 1
      -- Lose controls forever, plus the first two target payloads.
      if ops.any (fun o => !isWire o.kind) &&
          (!ops.any (fun o => o.id == target.id) || 2 < targetCopies) then
        let (next, _) ← (b.onFrame x "source".toUTF8 frame tick).run receiver
        b := next
    if ← hasOp receiver target then progressedWhileWriting := true
  ck.ok "lost payload is retried at least three times while every tick adds a post" (3 ≤ targetCopies)
  ck.ok "target arrives despite lost opening, all controls lost, and continuing producers" progressedWhileWriting
  ck.ok "replicated target settles to the same valid verdict"
    ((← (Store.getStatus target.id : SqlM Fact _).run receiver) ==
      (← (Store.getStatus target.id : SqlM Fact _).run source) &&
      (← (Store.getStatus target.id : SqlM Fact _).run receiver).any (fun v => match v with
        | .valid _ => true | _ => false))
  ck.ok "one catalog retry per session tick" (largestEmission ≤ 1)
  ck.ok "progress survives repeated sessions shorter than the target catalog position" (80 < reconnects)
  ck.ok "ongoing writes are retained at the source" (← hasOp source (message 1259))
  let peer := "authenticated-test-peer".toUTF8
  let before : Sweep := { after := 1, high := 9, active := true }
  ((RetryStore.sql (F := Fact)).save peer before).run source
  let blocked := { x with room := fun _ => some 0 }
  let (_, blockedOut) ← (a.sweep blocked session).run source
  ck.ok "zero output room retains the target position"
    (decide ((← ((RetryStore.sql (F := Fact)).load peer).run source) = before) && blockedOut.serve.isEmpty)
  let mut denied := a
  let mut leaked := false
  for _ in [0:12] do
    let (next, out) ← (denied.sweep (setup false) session).run source
    denied := next
    leaked := leaked || !out.serve.isEmpty
  ck.ok "fresh authorization excludes all catalog payloads after room removal" (!leaked)

end CatalogRetry

def main : IO UInt32 := do
  let ck ← Checks.new
  CatalogRetry.schemaChecks ck
  SqliteOpen.run ck
  CatalogRetry.retryChecks ck
  ck.finish "catalog-retry"
