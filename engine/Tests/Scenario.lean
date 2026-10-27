/-
A community's life on SQLite with real Ed25519, checked phase by phase
against what the laws promise: who is admitted, who may connect, who a
content key is sealed to, which removals stand, and that forgeries
fail. Then the same ops, shuffled and split into other transactions,
reach the same verdicts (order_free), equal to the model's and to the
spec's.
-/
import Tests.Lib

open Engine Community Tests

def C := ed25519

def status (x : Id) : SqlM Fact (Option (Verdict Fact)) := Store.getStatus x

def isValid (x : Id) : SqlM Fact Bool := do
  return match ← status x with | some (.valid _) => true | _ => false

def isInvalid (x : Id) : SqlM Fact Bool := do
  return match ← status x with | some .invalid => true | _ => false

def allow (c : Id) (d : Device) : SqlM Fact Bool := allowPeer (m := SqlM Fact) c d.pk

def sealedTo (c : Id) : SqlM Fact (List Key) := recipients (m := SqlM Fact) c

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/scenario"
  IO.FS.createDirAll dir
  for f in ["a.db", "a.db-wal", "a.db-shm", "b.db", "b.db-wal", "b.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
  let t ← Checks.new
  let fam := family C
  let db ← Db.openAt (dir ++ "/a.db")
  let run {α} (m : SqlM Fact α) : IO α := m.run db
  let recv (ops : List Op) : IO Unit := run (receive fam ops)

  -- People and devices. f2 is the founder's second device (linked);
  -- mallory is never invited.
  let f1 := Device.named "founder-1"
  let f2 := Device.named "founder-2"
  let a1 := Device.named "alice"
  let b1 := Device.named "bob"
  let c1 := Device.named "carol"
  let m1 := Device.named "mallory"
  let bearer (n : String) := Device.named ("bearer-" ++ n)

  -- Phase 1: found, invite, join, link, grant, post.
  let r := root f1
  let c := r.id
  let invA := invite c c f1 (bearer "a").pk false
  let invB := invite c c f1 (bearer "b").pk false
  let invC := invite c c f1 (bearer "c").pk false
  let invL := invite c c f1 (bearer "l").pk true
  let joinA := join c invA.id a1 (bearer "a").sk
  let joinB := join c invB.id b1 (bearer "b").sk
  let joinC := join c invC.id c1 (bearer "c").sk
  let joinL := join c invL.id f2 (bearer "l").sk
  let grantA := grant c c c joinA.id f1
  let postA := post c joinA.id a1 "k1".toUTF8 "hello".toUTF8
  -- Forgeries: mallory posting as alice; mallory joining without the
  -- link's bearer key; bob (not admin) granting himself admin.
  let forged := post c joinA.id m1 "k1".toUTF8 "I am alice".toUTF8
  let sneak := join c invB.id m1 m1.sk
  let selfGrant := grant c joinB.id joinB.id joinB.id b1
  let phase1 := [r, invA, invB, invC, invL, joinA, joinB, joinC, joinL, grantA, postA, forged, sneak, selfGrant]
  -- Deliver children before parents: the engine waits, then catches up.
  recv phase1.reverse

  for (name, o) in [("root", r), ("invite", invA), ("join alice", joinA), ("join bob", joinB),
      ("link founder-2", joinL), ("grant alice", grantA), ("alice's post", postA)] do
    t.ok s!"{name} is valid" (← run (isValid o.id))
  t.ok "mallory cannot post as alice" (← run (isInvalid forged.id))
  t.ok "mallory cannot join without the bearer key" (← run (isInvalid sneak.id))
  t.ok "a non-admin cannot grant admin" (← run (isInvalid selfGrant.id))
  for (name, d) in [("founder-1", f1), ("founder-2 (linked)", f2), ("alice", a1), ("bob", b1), ("carol", c1)] do
    t.ok s!"connects to {name}" (← run (allow c d))
  t.ok "refuses mallory" (!(← run (allow c m1)))
  let keys1 ← run (sealedTo c)
  t.ok "seals to every member device" ([f1, f2, a1, b1, c1].all fun d => keys1.contains d.enc)
  t.ok "seals to nobody else" (keys1.length == 5 && !keys1.contains m1.enc)

  -- Phase 2: alice (admin) and the founder remove each other; bob, not
  -- an admin, tries to remove carol; carol is untouched.
  let aRemovesF := remove c joinA.id grantA.id c a1
  let fRemovesA := remove c c c joinA.id f1
  let bRemovesC := remove c joinB.id joinB.id joinC.id b1
  recv [aRemovesF, fRemovesA, bRemovesC]
  t.ok "alice's removal of the founder stands" (← run (isValid aRemovesF.id))
  t.ok "the founder's removal of alice stands" (← run (isValid fRemovesA.id))
  t.ok "bob cannot remove carol" (← run (isInvalid bRemovesC.id))
  t.ok "refuses the removed founder" (!(← run (allow c f1)))
  t.ok "refuses the removed founder's linked device" (!(← run (allow c f2)))
  t.ok "refuses removed alice" (!(← run (allow c a1)))
  t.ok "still connects to bob" (← run (allow c b1))
  t.ok "still connects to carol" (← run (allow c c1))
  t.ok "alice's post survives her removal" (← run (isValid postA.id))
  let keys2 ← run (sealedTo c)
  t.ok "seals only to bob and carol" (keys2.length == 2 && keys2.contains b1.enc && keys2.contains c1.enc)

  -- Phase 3: the removed founder removes bob: it still stands. Carol
  -- removes herself (leave).
  let fRemovesB := remove c c c joinB.id f1
  let cLeaves := remove c joinC.id joinC.id joinC.id c1
  recv [fRemovesB, cLeaves]
  t.ok "a removed admin's removal still stands" (← run (isValid fRemovesB.id))
  t.ok "a member can remove itself" (← run (isValid cLeaves.id))
  t.ok "refuses bob" (!(← run (allow c b1)))
  t.ok "refuses carol" (!(← run (allow c c1)))
  t.ok "seals to nobody" ((← run (sealedTo c)).isEmpty)
  t.ok "queue is empty at rest" ((← run (dumpQueue (F := Fact))).isEmpty)

  -- Order: the same ops, shuffled, in other transactions, on another
  -- database, reach the same verdicts; and both equal the model's and
  -- the spec's.
  let all := phase1 ++ [aRemovesF, fRemovesA, bRemovesC, fRemovesB, cLeaves]
  let (shuffled, _) := (Rng.mk 7).shuffle all
  let db2 ← Db.openAt (dir ++ "/b.db")
  for chunk in [shuffled.take 5, (shuffled.drop 5).take 7, shuffled.drop 12] do
    (receive fam chunk).run db2
  let st1 ← run (dumpStatus (F := Fact))
  let st2 ← (dumpStatus (F := Fact)).run db2
  t.ok "same verdicts in any order and batching" (st1 == st2)
  let m := modelRun fam shuffled
  t.ok "SQLite verdicts equal the model's" (st1.all fun (x, v) => m.status x == some v)
  t.ok "every op has a verdict" (st1.length == all.length)
  t.ok "verdicts equal the spec's" (st1.all fun (x, v) => specOf fam m.ops all.length x == some v)
  t.finish "scenario"
