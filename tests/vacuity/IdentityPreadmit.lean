import tests.vacuity.IdentityLifecycle
import engine.sync.TakeLaws

/-! A removed member's node, holding the community's history, opens a
link a stranger made naming the stranger's own key (docs/TAKE-ROOM.md).
Real signed ops, a real Noise KK session between Bob's node and
Mallory's key, the node's own rooms view and the running connection
steps: the session takes the community and sends none of it; the
shipped room selection, on the same store, serves Bob's history. Then
the honest rejoin the take room keeps working: Dave, admitted after
Bob's removal, invites Bob back; Bob's session with Dave takes c, and
once Bob holds Dave's ops c turns synced and Bob is live. -/
namespace Vacuity.IdentityPreadmit
open Engine Codec Tests Connection Vacuity.Identity Vacuity.IdentityConnection
open Vacuity.IdentityLifecycle (localBob endpointB addr syncA heldFresh heldFreshReads catalogReads retryStoreReads)
open Community (ed25519)
set_option linter.defProp false

/-! ## Bob's node: removed, holding c's history -/

def oldOps := before ++ [removeB] ++ localBob
def bobAddr := "127.0.0.1:7448".toUTF8

/-! ## Mallory's link: c's id and her own key -/

def staticM := sha256 "vacuity-mallory-node".toUTF8
def pkM := sodium.suite.pub staticM
def eM := sha256 "vacuity-mallory-ephemeral".toUTF8
def eBob := sha256 "vacuity-bob-rejoin-ephemeral".toUTF8
def malAddr := "127.0.0.1:7449".toUTF8
def malloryInvite : Community.Invite :=
  ⟨c, sha256 "vacuity-mallory-invitation".toUTF8, pkM, [malAddr], sha256 "vacuity-mallory-bearer".toUTF8, false⟩
def rejoinSeed := sha256 "vacuity-bob-rejoin".toUTF8
def rejoinName := "Bob again".toUTF8
def unusedFresh := Bytes.digest "unused-node-seed".toUTF8
def rejoinRequest := malloryInvite.request (Community.Device.ofSeed rejoinSeed) pkB
def rejoinOps := (Community.joinOps malloryInvite rejoinSeed rejoinName pkB).ops

/-- What Bob's node writes on opening the link, as `join` runs. -/
def joinWrites : List Op :=
  (((Community.join malloryInvite rejoinSeed rejoinName unusedFresh).liftL : View F Community.Write).eval
    (run oldOps)).ops

/-- Bob dials Mallory with a hello carrying his request; Mallory answers. -/
structure Link where
  req : Op
  reply : Op

def link : Option Link := do
  let req ← Request.op sodium staticB pkM eBob (hello c bobAddr [rejoinRequest])
  let some (.request _ _ m1) := (decode req.body : Option Connection.Body) | none
  let reply ← Reply.op sodium req.id staticM pkB m1 eM
  pure ⟨req, reply⟩

def bobEph (l : Link) := Eph.op eBob l.req.id
def bobEst (l : Link) := Established.op l.reply.id l.req.id (bobEph l).id endpointB.id
def bobOps (l : Link) := oldOps ++ rejoinOps ++ [l.req, bobEph l, l.reply, bobEst l]
def db (l : Link) := run (bobOps l)
def cid (l : Link) := l.reply.id
def stored (l : Link) : List Op := (db l).stored.filterMap (db l).ops
def ix (l : Link) := Sync.Index.ofOps fam (stored l)

/-- The ops of c Bob's node holds: Alice's community, Bob's admission,
his message, the removal, his new request. -/
def history (l : Link) : List Op := (stored l).filter fun o => fam.room o == some c

/-! ## The law's premises, decided on the store -/

def linkOnly (l : Link) : Option (PLift (LinkOnly (db l) (cid l) c)) :=
  if hp : peersOf (eval (db l) (Connection.established.byConn.query [cid l])) = [pkM] then
    if ha : ((Community.allowPeer c pkM).liftL : View F Bool).eval (db l) = false then
      if hm : (meV c).eval (db l) = some pkB then
        if hk : ((linked c pkB pkM).liftL : View F Bool).eval (db l) = true then
          some ⟨by
            intro peer he; rw [hp, List.mem_singleton] at he; subst peer
            exact ⟨ha, pkB, hm, hk⟩⟩
        else none
      else none
    else none
  else none

/-- The connection as the node's steps read it: Bob dialed. -/
def conn0 : Sync.Conn := { (Sync.Conn.open true [] 0 0).conn with peerFloor := some 0 }
def carried (l : Link) := conn0.carry ((roomsV (cid l)).eval (db l))

def sendsNothing (l : Link) := do
  let ⟨hk⟩ ← linkOnly l
  pure (PLift.up (preadmit_sends_nothing fam {} (ix l) (db l) (cid l) c conn0
    (Sync.Msg.want ((history l).map Op.id)).op.bytes ((history l).map Op.id) 100 0 true hk))

def linkOnlyRooms (l : Link) := do
  let ⟨hk⟩ ← linkOnly l
  pure (PLift.up (linkOnly_rooms hk))

def refusedOnlyNotice (l : Link) := do
  let ⟨hk⟩ ← linkOnly l
  pure (PLift.up (refused_gets_only_notice fam {} (ix l) (db l) (cid l) c conn0
    (Sync.Msg.want ((history l).map Op.id)).op.bytes [] 100 0 true (linkOnly_refused hk)))

def linkedUnlive (l : Link) :=
  if hk : ((linked c pkB pkM).liftL : View F Bool).eval (db l) = true then
    some (PLift.up (linked_unlive (db l) hk)) else none

def roomsTake (l : Link) :=
  if h : ((roomsV (cid l)).eval (db l)).any (fun r => decide (r = Sync.Room.take c)) = true then
    some (PLift.up (rooms_take (db l) (by
      obtain ⟨rm, hm, he⟩ := List.any_eq_true.1 h
      exact (of_decide_eq_true he) ▸ hm)))
  else none

def roomForLaw (l : Link) :=
  let given := (givenOn (cid l)).eval (db l)
  if h : ((roomFor given c pkM).eval (db l)).any (fun r => decide (r = Sync.Room.take c)) = true then
    some (PLift.up (roomFor_law (db l) (given := given) (by
      obtain ⟨rm, hm, he⟩ := List.any_eq_true.1 h
      exact (of_decide_eq_true he) ▸ hm)))
  else none

/-! ## The running steps on that connection -/

def stepRun (l : Link) (m : Sync.Msg) : Sync.Step :=
  ((Sync.Conn.recv fam {} (ix l) (carried l) m.op.bytes 100 : Model F Sync.Step).run (db l)).1

/-- Mallory wants every op of c Bob holds. -/
def wantAll (l : Link) := stepRun l (.want ((history l).map Op.id))
/-- ... and then Bob's queue is served. -/
def served (l : Link) :=
  (((wantAll l).conn.serveOwed fam {} 1000000 [] : Model F _).run (db l)).1
/-- Mallory opens a round with a fingerprint of the whole window. -/
def fpRound (l : Link) := stepRun l (.rbsr c 1 [.fp ⟨⟨0, 0⟩, none⟩ 3 (sha256 "x".toUTF8)])
/-- Mallory opens a round listing ids, one of them Bob's message. -/
def idsRound (l : Link) := stepRun l (.rbsr c 1 [.ids ⟨⟨0, 0⟩, none⟩ [message.id]])
/-- Mallory's hello: Bob, the dialer, opens his rounds. -/
def helloStep (l : Link) := stepRun l (.hello 0)
def filedStep (l : Link) :=
  (((carried l).filedGive fam {} ((stored l).map Op.id) : Model F Sync.Step).run (db l)).1
def tickStep (l : Link) :=
  (((carried l).tickGive fam {} (ix l) 100 : Model F Sync.Step).run (db l)).1

/-- Mallory's own op of c, which Bob lacks. -/
def malloryOp := Community.invite c c mallory bearer.pk false
def offerStep (l : Link) := stepRun l (.hold c [malloryOp.id])
def takeStep (l : Link) :=
  ((Sync.Conn.recv fam {} (ix l) (carried l) malloryOp.bytes 100 : Model F Sync.Step).run (db l)).1

/-- No op of c among these, but wire ops. -/
def noneOfC (ops : List Op) : Bool := ops.all fun o => Sync.isWire o.kind || fam.room o != some c

/-- Every round message about c claims only empty id lists, and no have
about c names an id. -/
def blank (ops : List Op) : Bool := ops.all fun o => match Sync.Msg.ofOp o with
  | some (.rbsr r _ cs) => r != c || cs.all fun | .ids _ [] => true | _ => false
  | some (.hold r ids) => r != c || ids.isEmpty
  | _ => true

/-! ## The engine laws, applied to Bob's connection -/

def takesTaken (l : Link) :=
  if hroom : fam.room malloryOp = some c then
    if ht : has (carried l).takes c = true then
      if hw : Sync.isWire malloryOp.kind = false then
        some (PLift.up (Sync.recv_takes_taken fam {} (ix l) (carried l) 100 (db l) hroom ht hw))
      else none
    else none
  else none

def takeUnshown (l : Link) :=
  if hr : has (carried l).rooms c = false then
    if ho : fam.room message = some c then
      some (PLift.up (Sync.take_unshown fam (carried l) hr ho))
    else none
  else none

def answerBlank (l : Link) :=
  if hr : has (carried l).rooms c = false then
    some (PLift.up (Sync.Conn.answer_blank (P := ({} : Sync.Config).params) (ix := ix l) (f := 0) hr
      (.ids ⟨⟨0, 0⟩, none⟩ [message.id])))
  else none

def startBlank (l : Link) :=
  if hr : has (carried l).rooms c = false then
    some (PLift.up (Sync.start_take_blank {} (ix l) (carried l) 100 hr (k := 1)
      (cs := (Sync.window 0).map fun q => .ids q [])))
  else none

def rbsrBlank (l : Link) :=
  if hr : has (carried l).rooms c = false then
    some (PLift.up (Sync.onRbsr_take_blank {} (ix l) (carried l) 1 100 [.ids ⟨⟨0, 0⟩, none⟩ [message.id]] hr))
  else none

def takeOpens (l : Link) :=
  if ht : has (carried l).takes c = true then
    if hr : has (carried l).rooms c = false then
      if hd : ((carried l).due {} c 100 || (carried l).retake {} c) = true then
        some (PLift.up (Sync.take_opens {} (ix l) (carried l) c 100 0 rfl ((Engine.has_iff _ _).1 ht) hr hd))
      else none
    else none
  else none

/-- Mallory's side, syncing c from her own index, answers Bob's opening
with haves of all she holds. -/
def malConn : Sync.Conn := { (Sync.Conn.open false [c] 0 0).conn with peerFloor := some 0 }
def malIx := Sync.Index.ofOps fam [malloryOp]
def roundOffers :=
  if hr : has malConn.rooms c = true then
    if hf : malConn.oldRound c 1 = false then
      some (PLift.up (Sync.take_round_offers {} malIx malConn c 1 100 (Sync.window 0) hr hf (by simp [Sync.window])))
    else none
  else none

/-! ## A whole tick of Bob's node, with the family's hooks -/

def syncB : Sync.Sync F (Sync.HeldM F) :=
  { fam, cfg := {}, hooks := hooks fam sodium bobAddr, catalog := some (Sync.Catalog.held fam) }
theorem catalogReadsB : ∀ cat, syncB.catalog = some cat →
    Sync.Reads cat.ceiling ∧ ∀ i, Sync.Reads (cat.read i) := by
  intro cat hc; cases hc; exact ⟨fun _ => rfl, fun _ _ => rfl⟩
theorem retryStoreReadsB : ∀ store, syncB.retryStore = some store →
    (∀ peer, Sync.Reads (store.load peer)) ∧ (∀ peer cursor, Sync.Reads (store.save peer cursor)) := by
  intro store hs; cases hs

def heldBob (l : Link) : Sync.Held F := { log := bobOps l, db := db l }
def nodeB (l : Link) : Sync.Node :=
  { Sync.Node.boot fam (bobOps l) 0 with
    conns := [(cid l, conn0)]
    addrs := [(cid l, malAddr)]
    managed := [cid l] }
def tickB (l : Link) := ((nodeB l).onTick syncB 100).run (heldBob l)

/-- Bob's send key on the session, as his established fact holds it. -/
def sendKey (l : Link) : Option ByteArray :=
  match (db l).status (bobEst l).id with
  | some (.valid (.inr (.established _ _ _ _ sk _ _))) => some sk
  | _ => none

/-- The tick's frames to Mallory, opened with Bob's send key. -/
def tickPayloads (l : Link) : List Op :=
  match sendKey l with
  | none => []
  | some sk => (tickB l).1.2.send.flatMap fun (a, p) =>
    if a == malAddr && p[0]? == some Sync.sealedTag then
      match Frame.open sodium sk (p.extract 1 p.size) with
      | some (_, b) => ((decode b : Option (List ByteArray)).getD []).filterMap Op.decode
      | none => []
    else []

def reachesSession (l : Link) := do
  let ⟨hk⟩ ← linkOnly l
  pure (PLift.up (And.intro hk
    (preadmit_reaches_session heldFreshReads syncB sodium bobAddr rfl catalogReadsB retryStoreReadsB
      (.tick 100) (nodeB l) (heldBob l))))

/-! ## The negative control: the room selection as shipped -/

def shippedRooms (l : Link) : List Sync.Room :=
  (roomForShipped ((givenOn (cid l)).eval (db l)) c pkM).eval (db l)
def shippedConn (l : Link) := conn0.carry (shippedRooms l)
def shippedServed (l : Link) :=
  let w := ((Sync.Conn.recv fam {} (ix l) (shippedConn l) (Sync.Msg.want ((history l).map Op.id)).op.bytes 100
    : Model F Sync.Step).run (db l)).1
  ((w.conn.serveOwed fam {} 1000000 [] : Model F _).run (db l)).1

def shippedShows (l : Link) :=
  if hm : (meV c).eval (db l) = some pkB then
    if hk : ((linked c pkB pkM).liftL : View F Bool).eval (db l) = true then
      some (PLift.up (shipped_roomFor_shows (db l) (given := (givenOn (cid l)).eval (db l)) hm hk conn0))
    else none
  else none

/-! ## The honest rejoin: Dave, admitted after Bob's removal, invites him -/

def dave := Community.Device.named "vacuity-dave"
def staticD := sha256 "vacuity-dave-node".toUTF8
def pkD := sodium.suite.pub staticD
def eD := sha256 "vacuity-dave-ephemeral".toUTF8
def bearerD := Community.Device.named "vacuity-dave-invitation"
def inviteDave := Community.invite c c alice bearerD.pk false
def requestD := Community.request c inviteDave.id dave pkD bearerD.sk
def approvalD := Community.approve c requestD.id c alice
def admissionD := Community.admit c requestD.id approvalD.id
def daveIssue := Community.issue c admissionD.id dave pkD (sha256 "vacuity-dave-bearer".toUTF8) [malAddr]
def daveLink := daveIssue.2
def bobRequestD := daveLink.request (Community.Device.ofSeed rejoinSeed) pkB
def bobJoinD := (Community.joinOps daveLink rejoinSeed rejoinName pkB).ops
def approvalBob := Community.approve c bobRequestD.id admissionD.id dave
def admissionBob := Community.admit c bobRequestD.id approvalBob.id
/-- What Dave holds that Bob lacks: Dave's own admission, the invitation
to Bob, and Bob's new admission. -/
def daveChain := [inviteDave, requestD, approvalD, admissionD, daveIssue.1, approvalBob, admissionBob]

def daveSession : Option Link := do
  let req ← Request.op sodium staticB pkD eBob (hello c bobAddr [bobRequestD])
  let some (.request _ _ m1) := (decode req.body : Option Connection.Body) | none
  let reply ← Reply.op sodium req.id staticD pkB m1 eD
  pure ⟨req, reply⟩
def honestOps (l : Link) := oldOps ++ bobJoinD ++ [l.req, bobEph l, l.reply, bobEst l]
def honestDb (l : Link) := run (honestOps l)
def admittedDb (l : Link) := run (honestOps l ++ daveChain)

def completeTake (l : Link) :=
  if hm : (meV c).eval (honestDb l) = some pkB then
    if hp : peersOf (eval (honestDb l) (Connection.established.byConn.query [cid l])) = [pkD] then
      if hh : (heldV.eval (honestDb l)).any (fun r => decide (r = c)) = true then
        if ha : ((Community.allowPeer c pkD).liftL : View F Bool).eval (honestDb l) = false then
          if hk : ((linked c pkB pkD).liftL : View F Bool).eval (honestDb l) = true then
            some (PLift.up (rooms_complete_take (honestDb l) hm (by rw [hp]; exact List.mem_singleton_self _)
              (by obtain ⟨r, hr, he⟩ := List.any_eq_true.1 hh; exact (of_decide_eq_true he) ▸ hr) ha hk))
          else none
        else none
      else none
    else none
  else none

/-- Bob's take room takes Dave's admission of Bob as the running step does. -/
def honestTake (l : Link) :=
  let k := conn0.carry ((roomsV (cid l)).eval (honestDb l))
  ((Sync.Conn.recv fam {} (Sync.Index.ofOps fam []) k admissionBob.bytes 100 : Model F Sync.Step).run
    (honestDb l)).1

/-! ## The sibling: a cut node tells the device its user linked

Bob's node (its request names its own key) links a second device, Bob2,
on another node; Alice removes Bob's user, which cuts both. Bob's node
holds the removal and is no longer in c; on its session with Bob2's
node it carries the removal's notice and nothing else, so Bob2 learns
of its removal even if Bob's node is all it reaches. On a stranger's
session the same cut node carries nothing. -/

def bobReqK := Community.request c invitation.id bob pkB bearer.sk
def bobApprovalK := Community.approve c bobReqK.id c alice
def bobAdmissionK := Community.admit c bobReqK.id bobApprovalK.id
def linkBearer := Community.Device.named "vacuity-bob-link"
def bobLinkInv := Community.invite c bobAdmissionK.id bob linkBearer.pk true
def bob2 := Community.Device.named "vacuity-bob-second"
def staticB2 := sha256 "vacuity-bob2-node".toUTF8
def pkB2 := sodium.suite.pub staticB2
def eB2 := sha256 "vacuity-bob2-ephemeral".toUTF8
def b2Req := Community.request c bobLinkInv.id bob2 pkB2 linkBearer.sk
def b2Approval := Community.approve c b2Req.id bobAdmissionK.id bob
def b2Admission := Community.admit c b2Req.id b2Approval.id
def removeBea := Community.remove c c c bobAdmissionK.id alice
def siblingHistory := [r, invitation, bobReqK, bobApprovalK, bobAdmissionK, renamed, bobLinkInv, b2Req,
  b2Approval, b2Admission, removeBea]
def bobLocal := [Community.secret (sha256 "vacuity-bob".toUTF8), Community.accept c bob.pk, endpointB]

def siblingLink : Option Link := do
  let req ← Request.op sodium staticB pkB2 eBob (hello c bobAddr [])
  let some (.request _ _ m1) := (decode req.body : Option Connection.Body) | none
  let reply ← Reply.op sodium req.id staticB2 pkB m1 eB2
  pure ⟨req, reply⟩
def sibOps (l : Link) := siblingHistory ++ bobLocal ++ [l.req, bobEph l, l.reply, bobEst l]
def sibDb (l : Link) := run (sibOps l)
def sibCarried (l : Link) := conn0.carry ((roomsV (cid l)).eval (sibDb l))
def sibFiled (l : Link) :=
  (((sibCarried l).filedGive fam {} [removeBea.id] : Model F Sync.Step).run (sibDb l)).1

def unliveShared (l : Link) :=
  if hmn : (meV c).eval (sibDb l) = none then
    if hp : peersOf (eval (sibDb l) (Connection.established.byConn.query [cid l])) = [pkB2] then
      if hr : ((Community.allowPeer c pkB2).liftL : View F Bool).eval (sibDb l) = false then
        some (PLift.up (unlive_gets_only_shared_notice fam {} (Sync.Index.ofOps fam []) (sibDb l) (cid l) c
          conn0 .empty [removeBea.id] 100 0 true
          (fun ⟨me, hme, _⟩ => by rw [hmn] at hme; cases hme)
          (by intro peer he; rw [hp, List.mem_singleton] at he; subst peer; exact hr)))
      else none
    else none
  else none

def cutNotifies (l : Link) :=
  if hmn : (meV c).eval (sibDb l) = none then
    if hp : peersOf (eval (sibDb l) (Connection.established.byConn.query [cid l])) = [pkB2] then
      if hh : (heldV.eval (sibDb l)).any (fun r => decide (r = c)) = true then
        if hx : ((Community.removalsAt c pkB2).liftL : View F (List Id)).eval (sibDb l) = [removeBea.id] then
          if hc : ((Community.cutBy c).liftL : View F (List Id)).eval (sibDb l) = [removeBea.id] then
            if hg : has ((givenOn (cid l)).eval (sibDb l)) removeBea.id = false then
              some (PLift.up (cut_notifies (sibDb l) hmn (by rw [hp]; exact List.mem_singleton_self _)
                (by obtain ⟨r, hr, he⟩ := List.any_eq_true.1 hh; exact (of_decide_eq_true he) ▸ hr)
                (by rw [hx]; exact List.mem_singleton_self _) (by rw [hc]; exact List.mem_singleton_self _) hg))
            else none
          else none
        else none
      else none
    else none
  else none

/-- The same cut node, on a session with Mallory's key and no pending join. -/
def strangerCutOps (l : Link) := siblingHistory ++ bobLocal ++ [l.req, bobEph l, l.reply, bobEst l]

def main : IO UInt32 := do
  let t ← Checks.new
  let some l := link | IO.eprintln "Could not construct the Noise session with Mallory"; return 1
  t.ok "join on Mallory's link writes exactly the fresh join" (joinWrites == rejoinOps)
  t.ok "Bob's node holds c's history" ((history l).any (·.id == message.id) && (history l).any (·.id == renamed.id))
  t.ok "the session with Mallory is established" ((db l).status (bobEst l).id |>.isSome)
  t.ok "Bob's node is not live in c" (!((Community.allowPeer c pkB).liftL : View F Bool).eval (db l))
  t.ok "the handshake's trust rule takes Mallory (link clause)" (((trusts c pkB pkM).liftL : View F Bool).eval (db l))
  t.ok "the session carries c taken, nothing else" ((roomsV (cid l)).eval (db l) == [Sync.Room.take c])
  t.ok "link only" (linkOnly l).isSome
  t.ok "preadmit_sends_nothing applies" (sendsNothing l).isSome
  t.ok "refused_gets_only_notice applies" (refusedOnlyNotice l).isSome
  t.ok "linkOnly_rooms applies" (linkOnlyRooms l).isSome
  t.ok "linked_unlive applies" (linkedUnlive l).isSome
  t.ok "rooms_take applies" (roomsTake l).isSome
  t.ok "roomFor_law applies" (roomForLaw l).isSome
  t.ok "want for all of Bob's history: nothing queued" ((wantAll l).conn.owed.isEmpty && (wantAll l).send.isEmpty)
  t.ok "serving the queue sends nothing" ((served l).2.1.isEmpty && (served l).2.2.isEmpty)
  t.ok "hello: Bob opens c blank" (noneOfC (helloStep l).send && blank (helloStep l).send &&
    (helloStep l).send.any fun o => match Sync.Msg.ofOp o with | some (.rbsr r _ _) => r == c | _ => false)
  t.ok "a fingerprint round is answered blank" (noneOfC (fpRound l).send && blank (fpRound l).send)
  t.ok "an id round is answered blank, with no want" (noneOfC (idsRound l).send && blank (idsRound l).send &&
    (idsRound l).send.all fun o => match Sync.Msg.ofOp o with | some (.want _) => false | _ => true)
  t.ok "Bob's message, offered as a have, is not wanted: Bob holds it"
    ((stepRun l (.hold c [message.id, malloryOp.id])).send.all fun o => match Sync.Msg.ofOp o with
      | some (.want ids) => !ids.contains message.id | _ => true)
  t.ok "filed offers nothing of c" (noneOfC (filedStep l).send && blank (filedStep l).send)
  t.ok "tick sends nothing of c" (noneOfC (tickStep l).send && blank (tickStep l).send)
  t.ok "inbound: Mallory's have is wanted" ((offerStep l).send.any fun o =>
    match Sync.Msg.ofOp o with | some (.want ids) => ids.contains malloryOp.id | _ => false)
  t.ok "inbound: Mallory's op of c is taken" ((takeStep l).take.map (·.id) == [malloryOp.id])
  t.ok "recv_takes_taken applies" (takesTaken l).isSome
  t.ok "take_unshown applies" (takeUnshown l).isSome
  t.ok "Conn.answer_blank applies" (answerBlank l).isSome
  t.ok "start_take_blank applies" (startBlank l).isSome
  t.ok "onRbsr_take_blank applies" (rbsrBlank l).isSome
  t.ok "take_opens applies" (takeOpens l).isSome
  t.ok "take_round_offers applies" roundOffers.isSome
  t.ok "whole tick: link only where it starts" (reachesSession l).isSome
  t.ok "whole tick seals a frame for Mallory" (!(tickPayloads l).isEmpty)
  t.ok "whole tick's frame carries no op of c" (noneOfC (tickPayloads l) && blank (tickPayloads l))
  t.ok "shipped selection syncs c with Mallory" (shippedRooms l == [Sync.Room.sync c])
  t.ok "shipped_roomFor_shows applies" (shippedShows l).isSome
  t.ok "shipped selection serves Bob's history to Mallory (the finding)"
    ((shippedServed l).2.1 ++ (shippedServed l).2.2 |>.any (·.id == message.id))
  let some d := daveSession | IO.eprintln "Could not construct the Noise session with Dave"; return 1
  t.ok "Dave's chain validates" (daveChain.all fun o => match (admittedDb d).status o.id with
    | some (.valid _) => true | _ => false)
  t.ok "honest rejoin: the session with Dave carries c taken" ((roomsV (cid d)).eval (honestDb d) == [Sync.Room.take c])
  t.ok "rooms_complete_take applies" (completeTake d).isSome
  t.ok "honest rejoin: Bob's take room takes his admission" ((honestTake d).take.map (·.id) == [admissionBob.id])
  t.ok "honest rejoin: once Bob holds Dave's ops, c is synced"
    ((roomsV (cid d)).eval (admittedDb d) == [Sync.Room.sync c])
  t.ok "honest rejoin: Bob is live again" (((Community.allowPeer c pkB).liftL : View F Bool).eval (admittedDb d))
  let some sl := siblingLink | IO.eprintln "Could not construct the Noise session with Bob2"; return 1
  t.ok "sibling: Bob's chain and the link validate" ([bobAdmissionK, bobLinkInv, b2Admission, removeBea].all fun o =>
    match (sibDb sl).status o.id with | some (.valid _) => true | _ => false)
  t.ok "sibling: Bob's node is cut, no longer in c" ((meV c).eval (sibDb sl) == none &&
    (((Community.cutEntry c).liftL : View F _).eval (sibDb sl)).isSome)
  t.ok "sibling: the removal cuts Bob2 too" (((Community.removalsAt c pkB2).liftL : View F (List Id)).eval (sibDb sl) == [removeBea.id] &&
    ((Community.cutBy c).liftL : View F (List Id)).eval (sibDb sl) == [removeBea.id])
  t.ok "sibling: the session carries the removal's notice only"
    ((roomsV (cid sl)).eval (sibDb sl) == [Sync.Room.notice c removeBea.id])
  t.ok "sibling: the removal goes to Bob2" ((sibFiled sl).send.any (·.id == removeBea.id))
  t.ok "sibling: nothing else of c but its closure (no name op)" (!(sibFiled sl).send.any (·.id == renamed.id))
  t.ok "unlive_gets_only_shared_notice applies" (unliveShared sl).isSome
  t.ok "cut_notifies applies" (cutNotifies sl).isSome
  t.ok "a cut node gives a stranger's key nothing" ((roomsV (cid l)).eval (run (strangerCutOps l)) == [])
  t.finish "pre-admission sessions (removed node, stranger's link, honest rejoin, sibling notice)"

end Vacuity.IdentityPreadmit
