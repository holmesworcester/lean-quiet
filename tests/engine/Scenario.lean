/-
A community's life on SQLite with real Ed25519, checked phase by phase
against what the laws promise: who is admitted (requests, approvals,
admissions), who may connect, who a content key is sealed to, which
removals stand, and that forgeries fail. Then the same ops, shuffled and split into other transactions,
reach the same verdicts (order_free), equal to the model's and to the
spec's.
-/
import tests.engine.Lib

open Engine Community Tests

def C := ed25519

def status (x : Id) : SqlM Fact (Option (Verdict Fact)) := Store.getStatus x

def isValid (x : Id) : SqlM Fact Bool := do
  return match ← status x with | some (.valid _) => true | _ => false

def isInvalid (x : Id) : SqlM Fact Bool := do
  return match ← status x with | some .invalid => true | _ => false

/-- Whether c lets in device d's node (each test device is its own node). -/
def allow (c : Id) (d : Device) : SqlM Fact Bool := (allowPeer c (keyOf d)).run

def sealedTo (c : Id) : SqlM Fact (List Key) := (recipients c).run

def dialed (c : Id) : SqlM Fact (List Key) := (members c).run

/-- One fact, read as a list of one under its op's own key. -/
def getFact (x : Id) : SqlM Fact (Option Fact) := do
  let a ← (Lists.list { key := opKey x, limit := some 1 } : SqlM Fact (Answer Fact))
  return a.rows.head?.map (·.2)

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/scenario"
  IO.FS.createDirAll dir
  for f in ["a.db", "a.db-wal", "a.db-shm", "b.db", "b.db-wal", "b.db-shm", "c.db", "c.db-wal", "c.db-shm"] do
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
  let d1 := Device.named "dave"
  let e1 := Device.named "erin"
  let bearer (n : String) := Device.named ("bearer-" ++ n)

  -- Phase 1: found, invite, request, approve and admit (every request
  -- needs an approval: the founder approves alice, bob, carol and the
  -- link), grant, post.
  let r := root f1 (keyOf f1)
  let c := r.id
  let invA := invite c c f1 (bearer "a").pk false
  let invB := invite c c f1 (bearer "b").pk false
  let invC := invite c c f1 (bearer "c").pk false
  let invL := invite c c f1 (bearer "l").pk true
  let reqA := request c invA.id a1 (keyOf a1) (bearer "a").sk
  let reqB := request c invB.id b1 (keyOf b1) (bearer "b").sk
  let reqC := request c invC.id c1 (keyOf c1) (bearer "c").sk
  let reqL := request c invL.id f2 (keyOf f2) (bearer "l").sk
  let okA := approve c reqA.id c f1
  let okB := approve c reqB.id c f1
  let okC := approve c reqC.id c f1
  let joinA := admit c reqA.id [okA.id]
  let joinB := admit c reqB.id [okB.id]
  let joinC := admit c reqC.id [okC.id]
  -- No open link: an invitation needing no approval is refused, and a
  -- request with no approval is not admitted.
  let invZ := invite c c f1 (bearer "z").pk false 0
  let bareA := admit c reqA.id
  let okL := approve c reqL.id c f1
  let joinL := admit c reqL.id [okL.id]
  -- A link admitted with no approval, or approved by another user than
  -- the issuer's: refused.
  let bareL := admit c reqL.id
  let aliceOkL := approve c reqL.id joinA.id a1
  -- Dave asks to join through an invitation needing one approval; erin
  -- through one needing two. Nothing approves them yet.
  let invD := invite c c f1 (bearer "d").pk false 1
  let invE := invite c c f1 (bearer "e").pk false 2
  let reqD := request c invD.id d1 (keyOf d1) (bearer "d").sk
  let reqE := request c invE.id e1 (keyOf e1) (bearer "e").sk
  let bareD := admit c reqD.id
  -- An op in the old join's encoding (tag 2, the same shape as a
  -- request): it no longer decodes, so it is refused, not misread.
  let oldJoin : Op :=
    let body : ByteArray := ⟨(2 :: Codec.enc (m1.pk, (keyOf m1), ByteArray.empty, ByteArray.empty)).toArray⟩
    Op.make 2 [c, invB.id] body
  let grantA := grant c c c joinA.id f1
  let postA := post c joinA.id a1 "k1".toUTF8 "hello".toUTF8
  -- Forgeries: mallory posting as alice; mallory joining without the
  -- link's bearer key; bob (not admin) granting himself admin.
  let forged := post c joinA.id m1 "k1".toUTF8 "I am alice".toUTF8
  let sneak := request c invB.id m1 (keyOf m1) m1.sk
  let selfGrant := grant c joinB.id joinB.id joinB.id b1
  let phase1 := [r, invA, invB, invC, invL, reqA, reqB, reqC, reqL, okA, okB, okC, joinA, joinB, joinC,
    invZ, bareA, okL, joinL,
    bareL, aliceOkL, invD, invE, reqD, reqE, bareD, oldJoin, grantA, postA, forged, sneak, selfGrant]
  -- Deliver children before parents: the engine waits, then catches up.
  recv phase1.reverse

  for (name, o) in [("root", r), ("invite", invA), ("request alice", reqA), ("admit alice", joinA),
      ("admit bob", joinB), ("approve founder-2's link", okL), ("link founder-2", joinL),
      ("dave's request", reqD), ("grant alice", grantA), ("alice's post", postA)] do
    t.ok s!"{name} is valid" (← run (isValid o.id))
  t.ok "mallory cannot post as alice" (← run (isInvalid forged.id))
  t.ok "mallory cannot request without the bearer key" (← run (isInvalid sneak.id))
  t.ok "a link is not admitted without its approval" (← run (isInvalid bareL.id))
  t.ok "an invitation needing no approval is refused" (← run (isInvalid invZ.id))
  t.ok "a member request is not admitted without an approval" (← run (isInvalid bareA.id))
  t.ok "only the issuer's user approves a link" (← run (isInvalid aliceOkL.id))
  t.ok "a request needing an approval is not admitted without one" (← run (isInvalid bareD.id))
  t.ok "an op in the old join encoding is refused" (← run (isInvalid oldJoin.id))
  t.ok "a request alone does not connect dave" (!(← run (allow c d1)))
  t.ok "a request alone does not connect erin" (!(← run (allow c e1)))
  t.ok "a non-admin cannot grant admin" (← run (isInvalid selfGrant.id))
  for (name, d) in [("founder-1", f1), ("founder-2 (linked)", f2), ("alice", a1), ("bob", b1), ("carol", c1)] do
    t.ok s!"connects to {name}" (← run (allow c d))
  t.ok "refuses mallory" (!(← run (allow c m1)))
  let keys1 ← run (sealedTo c)
  t.ok "seals to every member device" ([f1, f2, a1, b1, c1].all fun d => keys1.contains (keyOf d))
  t.ok "seals to nobody else" (keys1.length == 5 && !keys1.contains (keyOf m1) && !keys1.contains (keyOf d1))
  let dial1 ← run (dialed c)
  t.ok "dials every member device, and nobody else"
    (dial1.length == 5 && [f1, f2, a1, b1, c1].all fun d => dial1.contains d.pk)
  t.ok "a fact is read by its own key" ((← run (getFact joinA.id)) == some (.admission c reqA.id a1.pk (keyOf a1)))
  t.ok "a pending request has its own key too" ((← run (getFact reqD.id)) != none)
  t.ok "an Invalid op has no row under its key" ((← run (getFact sneak.id)) == none)

  -- Phase 1b: approvals. Alice approves dave: admitted. Erin needs two
  -- distinct users: the founder's two devices are one user, so founder
  -- plus founder-2 is refused; founder plus alice admits her. Dave
  -- cannot approve his own request.
  let okD := approve c reqD.id joinA.id a1
  let joinD := admit c reqD.id [okD.id]
  let okE1 := approve c reqE.id c f1
  let okE2 := approve c reqE.id joinL.id f2
  let okE3 := approve c reqE.id joinA.id a1
  let sameUser := admit c reqE.id [okE1.id, okE2.id]
  let joinE := admit c reqE.id [okE1.id, okE3.id]
  let selfOk := approve c reqD.id joinD.id d1
  let short := admit c reqE.id [okE1.id]
  recv [joinE, short, sameUser, selfOk, okE3, okE2, okE1, joinD, okD]
  for (name, o) in [("alice's approval of dave", okD), ("dave's admission", joinD),
      ("founder-2's approval of erin", okE2), ("erin's admission", joinE)] do
    t.ok s!"{name} is valid" (← run (isValid o.id))
  t.ok "two approvals by one user are one" (← run (isInvalid sameUser.id))
  t.ok "one approval of two needed admits nobody" (← run (isInvalid short.id))
  t.ok "nobody approves their own request" (← run (isInvalid selfOk.id))
  t.ok "connects to dave once approved" (← run (allow c d1))
  t.ok "connects to erin once approved twice" (← run (allow c e1))
  let phase1b := [okD, joinD, okE1, okE2, okE3, sameUser, joinE, selfOk, short]

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
  t.ok "still connects to dave, approved by alice before her removal" (← run (allow c d1))
  t.ok "still connects to carol" (← run (allow c c1))
  t.ok "alice's post survives her removal" (← run (isValid postA.id))
  let keys2 ← run (sealedTo c)
  t.ok "seals only to bob, carol, dave and erin"
    (keys2.length == 4 && [b1, c1, d1, e1].all fun d => keys2.contains (keyOf d))

  -- Phase 3: the removed founder removes bob: it still stands. Carol
  -- removes herself (leave).
  let fRemovesB := remove c c c joinB.id f1
  let cLeaves := remove c joinC.id joinC.id joinC.id c1
  recv [fRemovesB, cLeaves]
  t.ok "a removed admin's removal still stands" (← run (isValid fRemovesB.id))
  t.ok "a member can remove itself" (← run (isValid cLeaves.id))
  t.ok "refuses bob" (!(← run (allow c b1)))
  t.ok "refuses carol" (!(← run (allow c c1)))
  t.ok "seals only to dave and erin" ((← run (sealedTo c)).length == 2)
  t.ok "queue is empty at rest" ((← run (dumpQueue (F := Fact))).isEmpty)

  -- Order: the same ops, shuffled, in other transactions, on another
  -- database, reach the same verdicts; and both equal the model's and
  -- the spec's.
  let all := phase1 ++ phase1b ++ [aRemovesF, fRemovesA, bRemovesC, fRemovesB, cLeaves]
  let (shuffled, _) := (Rng.mk 7).shuffle all
  let db2 ← Db.openAt (dir ++ "/b.db")
  for chunk in [shuffled.take 5, (shuffled.drop 5).take 17, shuffled.drop 22] do
    (receive fam chunk).run db2
  let st1 ← run (dumpStatus (F := Fact))
  let st2 ← (dumpStatus (F := Fact)).run db2
  t.ok "same verdicts in any order and batching" (st1 == st2)
  let m := modelRun fam shuffled
  t.ok "SQLite verdicts equal the model's" (st1.all fun (x, v) => m.status x == some v)
  t.ok "every op has a verdict" (st1.length == all.length)
  t.ok "verdicts equal the spec's" (st1.all fun (x, v) => specOf fam m.ops all.length x == some v)
  -- Sync scope, on SQLite: with admit ops declared local, sync offers
  -- every stored op but those; a peer's job loses them; this node's own
  -- job keeps them.
  let famL : Family Fact := { fam with scope := fun o => if o.kind = 11 then .local else fam.scope o }
  let isAdmit (o : Op) := o.kind == 11
  let offered ← run (offer famL (all.map (·.id)))
  t.ok "sync offers no local op" (!offered.any isAdmit)
  t.ok "sync offers every stored shared op" (all.all fun o => isAdmit o || offered.contains o)
  let db3 ← Db.openAt (dir ++ "/c.db")
  (receive famL (intake famL false phase1)).run db3
  let fromPeer ← (dumpOps (F := Fact)).run db3
  t.ok "a peer's local ops are dropped" (!fromPeer.any isAdmit && fromPeer.any (·.id == reqA.id))
  (receive famL (intake famL true [joinA])).run db3
  t.ok "this node's own local op is kept" ((← (dumpOps (F := Fact)).run db3).any (·.id == joinA.id))
  t.finish "scenario"
