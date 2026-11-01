/-
A community's life on SQLite with real Ed25519, checked phase by phase
against what the laws promise: who is admitted (requests, approvals,
admissions), who may connect, who a content key is sealed to, which
removals stand, and that forgeries fail. Then the same ops, shuffled and split into other transactions,
reach the same verdicts (order_free), equal to the model's and to the
spec's.
-/
import tests.engine.Lib
import tests.engine.Stream

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
  let joinA := admit c reqA.id okA.id
  let joinB := admit c reqB.id okB.id
  let joinC := admit c reqC.id okC.id
  -- No open link: a request with no approval is not admitted (an admit
  -- citing none, composed by hand: `admit` always cites one).
  let bareA := mkOp [c, reqA.id] .admit
  let okL := approve c reqL.id c f1
  let joinL := admit c reqL.id okL.id
  -- A link admitted with no approval, or approved by another user than
  -- the issuer's: refused.
  let bareL := mkOp [c, reqL.id] .admit
  let aliceOkL := approve c reqL.id joinA.id a1
  -- Dave and erin ask to join. Nothing approves them yet.
  let invD := invite c c f1 (bearer "d").pk false
  let invE := invite c c f1 (bearer "e").pk false
  let reqD := request c invD.id d1 (keyOf d1) (bearer "d").sk
  let reqE := request c invE.id e1 (keyOf e1) (bearer "e").sk
  let bareD := mkOp [c, reqD.id] .admit
  -- An op in the old join's encoding (tag 2, the same shape as a
  -- request): it no longer decodes, so it is refused, not misread.
  let oldJoin : Op :=
    let body : ByteArray := ⟨(2 :: Codec.enc (m1.pk, (keyOf m1), ByteArray.empty, ByteArray.empty)).toArray⟩
    Op.make 2 [c, invB.id] body
  -- An invitation in the encoding before thresholds were removed (one
  -- with threshold 1, signed as it was then): it no longer decodes, so
  -- it is refused, and no request can redeem it.
  let oldInvite : Op :=
    let reqs := [c, c]
    let old (s : ByteArray) : List UInt8 := 1 :: Codec.enc ((bearer "o").pk, false, (1 : Nat), s)
    -- what the signature covered: the domain, the requirements, then the
    -- old body with its signature blanked (a tuple encodes as its parts)
    let s := edSign f1.sk ⟨(Codec.enc ("quiet/attest/v1".toUTF8, reqs) ++ old .empty).toArray⟩
    Op.make 1 reqs ⟨(old s).toArray⟩
  let oldReq := request c oldInvite.id m1 (keyOf m1) (bearer "o").sk
  let grantA := grant c c c joinA.id f1
  let postA := post c joinA.id a1 "k1".toUTF8 "hello".toUTF8 1 0
  -- Forgeries: mallory posting as alice; mallory joining without the
  -- link's bearer key; bob (not admin) granting himself admin.
  let forged := post c joinA.id m1 "k1".toUTF8 "I am alice".toUTF8 1 0
  let sneak := request c invB.id m1 (keyOf m1) m1.sk
  let selfGrant := grant c joinB.id joinB.id joinB.id b1
  let phase1 := [r, invA, invB, invC, invL, reqA, reqB, reqC, reqL, okA, okB, okC, joinA, joinB, joinC,
    bareA, okL, joinL,
    bareL, aliceOkL, invD, invE, reqD, reqE, bareD, oldJoin, oldInvite, oldReq, grantA, postA, forged, sneak,
    selfGrant]
  -- Deliver children before parents: the engine waits, then catches up.
  recv phase1.reverse

  for (name, o) in [("root", r), ("invite", invA), ("request alice", reqA), ("admit alice", joinA),
      ("admit bob", joinB), ("approve founder-2's link", okL), ("link founder-2", joinL),
      ("dave's request", reqD), ("grant alice", grantA), ("alice's post", postA)] do
    t.ok s!"{name} is valid" (← run (isValid o.id))
  t.ok "mallory cannot post as alice" (← run (isInvalid forged.id))
  t.ok "mallory cannot request without the bearer key" (← run (isInvalid sneak.id))
  t.ok "a link is not admitted without its approval" (← run (isInvalid bareL.id))
  t.ok "a member request is not admitted without an approval" (← run (isInvalid bareA.id))
  t.ok "only the issuer's user approves a link" (← run (isInvalid aliceOkL.id))
  t.ok "dave's request is not admitted without an approval" (← run (isInvalid bareD.id))
  t.ok "an op in the old join encoding is refused" (← run (isInvalid oldJoin.id))
  t.ok "an invitation with a threshold (the old encoding) is refused" (← run (isInvalid oldInvite.id))
  t.ok "and a request redeeming it is refused" (← run (isInvalid oldReq.id))
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

  -- Phase 1b: approvals. One approval admits: alice approves dave, and
  -- founder-2 (the founder's second device) approves erin. An admit
  -- must cite exactly one approval, of its own request: two (even of
  -- two users), or an approval of another request, are refused. Dave
  -- cannot approve his own request, and founder-2 cannot approve a link
  -- of its own device.
  let okD := approve c reqD.id joinA.id a1
  let joinD := admit c reqD.id okD.id
  let okE1 := approve c reqE.id c f1
  let okE2 := approve c reqE.id joinL.id f2
  let okE3 := approve c reqE.id joinA.id a1
  let joinE := admit c reqE.id okE2.id
  let twoOk := mkOp [c, reqE.id, okE1.id, okE3.id] .admit
  let otherReq := admit c reqE.id okD.id
  let selfOk := approve c reqD.id joinD.id d1
  let invL2 := invite c c f1 (bearer "l2").pk true
  let reqL2 := request c invL2.id f2 (keyOf f2) (bearer "l2").sk
  let selfLink := approve c reqL2.id joinL.id f2
  let selfLinkIn := admit c reqL2.id selfLink.id
  recv [selfLinkIn, selfLink, reqL2, invL2, joinE, otherReq, twoOk, selfOk, okE3, okE2, okE1, joinD, okD]
  for (name, o) in [("alice's approval of dave", okD), ("dave's admission", joinD),
      ("founder-2's approval of erin", okE2), ("erin's admission by founder-2's approval", joinE),
      ("the founder's approval of erin", okE1), ("alice's approval of erin", okE3)] do
    t.ok s!"{name} is valid" (← run (isValid o.id))
  t.ok "an admit citing two approvals is refused" (← run (isInvalid twoOk.id))
  t.ok "an admit citing another request's approval is refused" (← run (isInvalid otherReq.id))
  t.ok "nobody approves their own request" (← run (isInvalid selfOk.id))
  t.ok "a device does not approve its own link" (← run (isInvalid selfLink.id))
  t.ok "so its link is not admitted" (← run (isInvalid selfLinkIn.id))
  t.ok "connects to dave once approved" (← run (allow c d1))
  t.ok "connects to erin once approved" (← run (allow c e1))
  let phase1b := [okD, joinD, okE1, okE2, okE3, joinE, twoOk, otherReq, selfOk, invL2, reqL2, selfLink, selfLinkIn]

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
  t.ok "still connects to dave, approved by alice, now removed" (← run (allow c d1))
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

  -- Phase 3b: removal takes a member off the network, not its power to
  -- act. Alice, removed, still invites and approves: her ops stay
  -- Valid, and frank, whom they admit, is let in. So is a fresh device
  -- on alice's own node, named in a request she invites and approves:
  -- her node key is let in again. That is the README's stated gap
  -- (removed users are not yet proven kept off the network); this
  -- check pins today's behaviour until the fix is chosen.
  let frank := Device.named "frank"
  let aliceAgain := Device.named "alice-again"
  let invF := invite c joinA.id a1 (bearer "f").pk false
  let reqF := request c invF.id frank (keyOf frank) (bearer "f").sk
  let okF := approve c reqF.id joinA.id a1
  let joinF := admit c reqF.id okF.id
  let invR := invite c joinA.id a1 (bearer "r").pk false
  let reqR := request c invR.id aliceAgain (keyOf a1) (bearer "r").sk
  let okR := approve c reqR.id joinA.id a1
  let joinR := admit c reqR.id okR.id
  recv [joinR, okR, reqR, invR, joinF, okF, reqF, invF]
  for (name, o) in [("removed alice's invitation", invF), ("removed alice's approval", okF),
      ("frank's admission", joinF), ("alice-again's admission", joinR)] do
    t.ok s!"{name} is valid" (← run (isValid o.id))
  t.ok "connects to frank, approved by removed alice" (← run (allow c frank))
  t.ok "stated gap: removed alice's own invitation and approval let her node in again" (← run (allow c a1))
  let phase3b := [invF, reqF, okF, joinF, invR, reqR, okR, joinR]
  t.ok "queue is empty at rest" ((← run (dumpQueue (F := Fact))).isEmpty)

  -- Order: the same ops, shuffled, in other transactions, on another
  -- database, reach the same verdicts; and both equal the model's and
  -- the spec's.
  let all := phase1 ++ phase1b ++ [aRemovesF, fRemovesA, bRemovesC, fRemovesB, cLeaves] ++ phase3b
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
  let offered ← streamOps famL db
  t.ok "sync offers no local op" (!offered.any isAdmit)
  t.ok "sync offers every stored shared op" (all.all fun o => isAdmit o || offered.contains o)
  let db3 ← Db.openAt (dir ++ "/c.db")
  (receive famL (intake famL false phase1)).run db3
  let fromPeer ← (dumpOps (F := Fact)).run db3
  t.ok "a peer's local ops are dropped" (!fromPeer.any isAdmit && fromPeer.any (·.id == reqA.id))
  (receive famL (intake famL true [joinA])).run db3
  t.ok "this node's own local op is kept" ((← (dumpOps (F := Fact)).run db3).any (·.id == joinA.id))
  t.finish "scenario"
