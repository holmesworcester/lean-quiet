/- Real signed ops, SQLite, sender policy, arrival permutations and a
backwards-compatible index migration. No receiver-side grouping heuristic. -/
import tests.engine.Lib

open Engine Community Tests

namespace ClumpsTest

def additions : Fact → List ByteArray := keysOf
  [message.rootsByKey, message.childrenByKey, received.rootsByKey, received.childrenByKey]

def nonce (i : Nat) : ByteArray := (sha256 s!"clump-{i}".toUTF8).extract 0 24

def fact (db : Db) (id : Id) : IO (Option Fact) := (Clump.fact id).run (m := SqlM Fact) |>.run db

def group (f : Option Fact) : Option (Option Id) :=
  match f with | some (.message _ _ _ _ _ _ _ g) => some g | _ => none

def run (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  for file in ["a", "b", "migration"] do
    for suffix in ["", "-wal", "-shm"] do
      let path := s!"{dir}/{file}.db{suffix}"
      if ← System.FilePath.pathExists path then IO.FS.removeFile path
  let fam := family ed25519
  let db ← Db.openAt (dir ++ "/a.db")
  let other ← Db.openAt (dir ++ "/b.db")
  let alice := Device.named "clump-alice"
  let linked := Device.named "clump-alice-phone"
  let bob := Device.named "clump-bob"
  let bearer := Device.named "clump-invite"
  let r := root alice (keyOf alice)
  let c := r.id
  let key := sha256 "clump-content-key".toUTF8
  let kid := kidOf cryptoSeal key
  let inv := invite c c alice bearer.pk false
  let req := request c inv.id bob (keyOf bob) bearer.sk
  let ap := approve c req.id c alice
  let adm := admit c req.id [ap.id]
  let link := invite c c alice bearer.pk true
  let lr := request c link.id linked (keyOf linked) bearer.sk
  let la := approve c lr.id c alice
  let ladm := admit c lr.id [la.id]
  let setup := [r, contentKey c key, inv, req, ap, adm, link, lr, la, ladm]
  (receive fam setup).run db
  (receive fam setup.reverse).run other
  let sendAt (who : Device) (admission : Id) (time i : Nat) : IO Op := do
    let w ← ((send c admission who key (nonce i) s!"message-{i}".toUTF8 time).run (m := SqlM Fact)).run db
    let p := w.ops.head!
    (receive fam w.ops).run db
    return p
  let first ← sendAt alice c 100 1
  ck.ok "first send is a root" (group (← fact db first.id) == some none)
  let second ← sendAt alice c 101 2
  ck.ok "sender explicitly cites its root" (second.reqs == [c, c, first.id] && group (← fact db second.id) == some (some first.id))
  let phone ← sendAt linked ladm.id 102 3
  ck.ok "linked devices continue the same user's clump" (group (← fact db phone.id) == some (some first.id))
  let within ← sendAt alice c 104 4
  let expired ← sendAt alice c 105 5
  ck.ok "five minutes is a total span from the root, not from the last child"
    (group (← fact db within.id) == some (some first.id) && group (← fact db expired.id) == some none)
  let backwards ← sendAt alice c 104 6
  ck.ok "clock moving backwards starts a root" (group (← fact db backwards.id) == some none)
  let interloper ← sendAt bob adm.id 104 7
  let resumed ← sendAt alice c 104 8
  ck.ok "an intervening author starts a new root" (group (← fact db resumed.id) == some none)
  -- A peer may receive Bob between Alice's root and children. Grouping is
  -- still the signed root reference, never adjacent-arrival inference.
  (receive fam [phone, interloper, second]).run other
  ck.ok "a child waits for its missing root" ((← fact other second.id).isNone)
  (receive fam [first]).run other
  ck.ok "out-of-order arrivals retain the sender's declared groups"
    (group (← fact other second.id) == some (some first.id) && group (← fact other phone.id) == some (some first.id))
  let children ← ((readableClumps c (some first.id) (some 2)).run (m := SqlM Fact)).run db
  let roots ← ((readableClumps c none (some 2)).run (m := SqlM Fact)).run db
  ck.ok "child and root lists are separately bounded and counted"
    (children.rows.length == 2 && children.total == 3 && roots.rows.length == 2 && roots.total == 5)
  let rogue := sealedPost c adm.id bob key (nonce 20) "foreign".toUTF8 20 104 (some first.id)
  let nested := sealedPost c c alice key (nonce 21) "nested".toUTF8 21 104 (some second.id)
  let remoteRoot := root alice "different-community".toUTF8
  let remoteMsg := sealedPost remoteRoot.id remoteRoot.id alice key (nonce 22) "other".toUTF8 1 104
  let cross := sealedPost c c alice key (nonce 23) "cross".toUTF8 22 104 (some remoteMsg.id)
  let forged := Op.make second.kind [c, c, resumed.id] second.body
  (receive fam [rogue, nested, remoteRoot, remoteMsg, cross, forged]).run db
  for (label, op) in [("other user", rogue), ("nested child", nested), ("other community", cross), ("retargeted signature", forged)] do
    ck.ok s!"rejects {label}" ((← (Store.getStatus op.id : SqlM Fact (Option (Verdict Fact))).run db) == some .invalid)
  let saturated := sealedPost c c alice key (nonce 30) "cap-root".toUTF8 countCap 106
  (receive fam [saturated, receipt saturated.id 1]).run db
  let satChild := sealedPost c c alice key (nonce 31) "cap-child".toUTF8 countCap 107 (some saturated.id)
  (receive fam [satChild, receipt satChild.id 2]).run db
  let satRows ← ((readableClumps c (some saturated.id)).run (m := SqlM Fact)).run db
  ck.ok "saturated children keep receipt order and group membership"
    (satRows.rows.map (·.1) == [(recKey 2 satChild.id, satChild.id)])
  let oldFact := Fact.message c c alice.pk kid "sealed".toUTF8 1 100
  let oldBytes := ByteArray.mk (21 :: Codec.enc (c, c, alice.pk, kid, "sealed".toUTF8, (1 : Nat), (100 : Nat))).toArray
  ck.ok "legacy root bytes decode and re-encode identically"
    ((Codec.decode oldBytes : Option Fact) == some oldFact && Codec.encode oldFact == oldBytes)
  let childFact := Fact.message c c alice.pk kid "sealed".toUTF8 2 101 (some first.id)
  ck.ok "child codec carries its root in both codec interpreters"
    ((Codec.decode (Codec.encode childFact) : Option Fact) == some childFact &&
      (Fact.dec (Fact.enc childFact)).map (·.1) == some childFact)
  let migration ← Db.openAt (dir ++ "/migration.db")
  let legacy := { fam with keys := fun f => fam.keys f |>.filter (fun k => !(additions f).contains k) }
  let history := (List.range 300).map fun i => sealedPost c c alice key (nonce (100 + i)) s!"old-{i}".toUTF8 i (80+i)
  (receive legacy (setup ++ history)).run migration
  let bytesBefore ← migration.query "SELECT id, bytes FROM ops ORDER BY id" #[]
  let migrated ← (reindexOnce "clumps-test" additions).run migration
  let allRoots ← ((readableClumps c none (some 7)).run (m := SqlM Fact)).run migration
  let twice ← (reindexOnce "clumps-test" additions).run migration
  ck.ok "paged migration backfills old roots without duplicates or lost history"
    (migrated && !twice && allRoots.total == 300 && allRoots.rows.length == 7 &&
      bytesBefore == (← migration.query "SELECT id, bytes FROM ops ORDER BY id" #[]))
  -- A bad persisted row must roll back even filings from earlier pages.
  let invalidId := ByteArray.mk (Array.replicate 32 255)
  discard <| migration.query "INSERT INTO status (id, verdict) VALUES (?, ?)" #[invalidId, "invalid".toUTF8]
  let extra := "test-uncommitted-index".toUTF8
  let refused ← try
    discard <| (reindexOnce (F := Fact) "broken-migration" (fun _ => [extra])).run migration
    pure false
  catch _ => pure true
  let filed ← migration.query "SELECT id FROM idx WHERE k = ?" #[extra]
  let marker ← migration.query "SELECT version FROM index_versions WHERE version = ?" #["broken-migration".toUTF8]
  ck.ok "failed migration rolls back its filings and completion marker" (refused && filed.isEmpty && marker.isEmpty)
  discard <| migration.query "DELETE FROM status WHERE id = ?" #[invalidId]
  let oldValidator := { legacy with validate := fun o fs =>
    if o.kind == 23 && o.reqs.length == 3 then none else fam.validate o fs }
  let oldChild := sealedPost c c alice key (nonce 999) "received-before-upgrade".toUTF8 301 104 (some history.head!.id)
  let reaction := react c adm.id oldChild.id bob "❤️".toUTF8 104
  (receive oldValidator [oldChild, reaction]).run migration
  ck.ok "fixture exercises a child refused by the old installed validator"
    ((← (Store.getStatus oldChild.id : SqlM Fact (Option (Verdict Fact))).run migration) == some .invalid)
  discard <| (reindexOnce "validator-upgrade" additions (some fam)).run migration
  ck.ok "upgrade retries previously refused new ops and their dependents without data loss"
    (group (← fact migration oldChild.id) == some (some history.head!.id) && (← fact migration reaction.id).isSome)

end ClumpsTest

def main (args : List String) : IO UInt32 := do
  let ck ← Checks.new
  ClumpsTest.run (args.headD "out/clumps") ck
  ck.finish "clumps"
