import tests.vacuity.IdentityFixture
import app.Proofs

namespace Vacuity.IdentityConnection
open Engine Engine.Sync Codec Tests
open Community (ed25519)
open Vacuity.Identity
open Connection
set_option linter.defProp false

deriving instance DecidableEq for Connection.Eph.Fact
deriving instance DecidableEq for Connection.Eph.Body
deriving instance DecidableEq for Connection.Request.Fact
deriving instance DecidableEq for Connection.Request.Body
deriving instance DecidableEq for Connection.Opened.Fact
deriving instance DecidableEq for Connection.Opened.Body
deriving instance DecidableEq for Connection.Reply.Fact
deriving instance DecidableEq for Connection.Reply.Body
deriving instance DecidableEq for Connection.Established.Fact
deriving instance DecidableEq for Connection.Established.Body
deriving instance DecidableEq for Connection.Send.Fact
deriving instance DecidableEq for Connection.Send.Body
deriving instance DecidableEq for Connection.Recv.Fact
deriving instance DecidableEq for Connection.Recv.Body
deriving instance DecidableEq for Connection.Given.Fact
deriving instance DecidableEq for Connection.Given.Body
deriving instance DecidableEq for Connection.Fact
deriving instance DecidableEq for Connection.Body
deriving instance DecidableEq, BEq for Engine.Sync.Room

def fam := Connection.node ed25519 sodium

def load : List Op → DB F
  | [] => DB.empty
  | o :: os => ingestS o (load os)
theorem loadReach (ops : List Op) : Reach fam ops (load ops) := by
  induction ops with
  | nil => exact .empty
  | cons o os ih => exact .ingest o ih

def run (ops : List Op) := drainS fam 500 (load ops)
theorem runReach (ops : List Op) : Reach fam ops (run ops) := reach_drain (loadReach ops) 500
theorem runInv (ops : List Op) : Inv fam (run ops) := reach_inv (runReach ops)

def staticA := sha256 ("test node ".toUTF8 ++ alice.pk)
def staticB := sha256 ("test node ".toUTF8 ++ bob.pk)
def eA := sha256 "vacuity-responder-ephemeral".toUTF8
def eB := sha256 "vacuity-initiator-ephemeral".toUTF8
def endpointA := Community.endpoint staticA
def pkA := sodium.suite.pub staticA
def pkB := sodium.suite.pub staticB
def myOps := [Community.secret (sha256 "vacuity-alice".toUTF8),Community.accept c alice.pk,endpointA]

structure Session where
  req : Op
  reply : Op
  m1 : ByteArray
  m2 : ByteArray
  hash : ByteArray
  sendKey : ByteArray
  recvKey : ByteArray

def session : Option Session := do
  let req ← Request.op sodium staticB pkA eB (hello c "127.0.0.1:7447".toUTF8 [requestB])
  let some (.request _ _ m1) := (decode req.body : Option Connection.Body) | none
  let reply ← Reply.op sodium req.id staticA pkB m1 eA
  let some (.connection m2) := (decode reply.body : Option Connection.Body) | none
  let (st,re,_) ← Noise.read1 sodium.suite prologue staticA pkB m1
  let (sr,_) ← Noise.write2 sodium.suite st eA pkB re .empty
  pure ⟨req,reply,m1,m2,sr.h,sr.send.k,sr.recv.k⟩

def eph (s : Session) := Eph.op eA s.reply.id
def opened (s : Session) := Opened.op s.req.id endpointA.id
def established (s : Session) := Established.op s.reply.id s.req.id (eph s).id endpointA.id

def activeOps (s : Session) := before ++ myOps ++ [s.req,s.reply,eph s,opened s,established s]
def cutOps (s : Session) := activeOps s ++ [removeB]

def projection (s : Session) := if hq : (run (activeOps s)).queue = [] then
  some (PLift.up (sum_project_node (runInv (activeOps s)) hq)) else none

def nodeConnect (s : Session) := if hq : (run (activeOps s)).queue = [] then
  some (PLift.up (connect_iff_node (runInv (activeOps s)) hq c pkB)) else none

def nodeMembers (s : Session) := if hq : (run (activeOps s)).queue = [] then
  some (PLift.up (members_iff_node (runInv (activeOps s)) hq c bob.pk)) else none

def nodeRecipients (s : Session) := if hq : (run (activeOps s)).queue = [] then
  some (PLift.up (recipients_iff_node (runInv (activeOps s)) hq c pkB)) else none

def nodeSettles (s : Session) :=
  if hd : (activeOps s).all (fun a => (activeOps s).all fun b => decide (a.id = b.id → a = b)) = true then
    some (PLift.up (node_settles (by
      intro a ha b hb hab
      have h1 := (List.all_eq_true.1 hd) a ha
      have h2 := (List.all_eq_true.1 h1) b hb
      exact of_decide_eq_true h2 hab) (loadReach (activeOps s))))
  else none

def readsMembers := Community.reads_members c
def readsRecipients := Community.reads_recipients c

def wireKinds (s : Session) := if h : Connection.scopeOf s.req = .conn then
  some (PLift.up (wire_kinds s.req h)) else none

def localKinds (s : Session) := if h : ¬ ((eph s).kind = 33 ∨ (eph s).kind = 35) then
  some (PLift.up (local_kinds (eph s) h)) else none

def meNode (s : Session) := if hm : (meV c).eval (run (activeOps s)) = some pkA then
  some (PLift.up (meV_node (run (activeOps s)) hm)) else none

def trustsLive (s : Session) :=
  if h : ((Community.allowPeer c pkA).liftL : View F Bool).eval (run (activeOps s)) = true then
    some (PLift.up (trusts_live (run (activeOps s)) (peer := pkB) h)) else none

def roomsModel (s : Session) := some (PLift.up (rooms_model (run (activeOps s)) s.reply.id))

def roomsTrusted (s : Session) :=
  if h : ((roomsV s.reply.id).eval (run (activeOps s))).any (fun r => decide (r = Room.sync c)) = true then
    some (PLift.up (rooms_trusted (run (activeOps s)) (by
      obtain ⟨rm,hm,he⟩ := List.any_eq_true.1 h
      exact (of_decide_eq_true he) ▸ hm)))
  else none

def roomsComplete (s : Session) :=
  if hm : (meV c).eval (run (activeOps s)) = some pkA then
    if hp : peersOf (eval (run (activeOps s)) (Connection.established.byConn.query [s.reply.id])) = [pkB] then
      if hh : (heldV.eval (run (activeOps s))).any (fun r => decide (r = c)) = true then
        if ht : ((Community.allowPeer c pkB).liftL : View F Bool).eval (run (activeOps s)) = true then
          some (PLift.up (rooms_complete (run (activeOps s)) hm (by rw [hp]; exact List.mem_singleton_self _)
            (by obtain ⟨r,hr,he⟩ := List.any_eq_true.1 hh; exact (of_decide_eq_true he) ▸ hr) ht))
        else none
      else none
    else none
  else none

def liveIn (s : Session) : Option (PLift (LiveIn (run (cutOps s)) c)) :=
  if hm : (meV c).eval (run (cutOps s)) = some pkA then
    if hl : ((Community.allowPeer c pkA).liftL : View F Bool).eval (run (cutOps s)) = true then
      some ⟨by intro me he; rw [hm] at he; cases he; exact hl⟩
    else none
  else none

def refused (s : Session) : Option (PLift (Refused (run (cutOps s)) s.reply.id c)) :=
  if hp : peersOf (eval (run (cutOps s)) (Connection.established.byConn.query [s.reply.id])) = [pkB] then
    if hr : ((Community.allowPeer c pkB).liftL : View F Bool).eval (run (cutOps s)) = false then
      some ⟨by intro peer he; rw [hp, List.mem_singleton] at he; subst peer; exact hr⟩
    else none
  else none

def roomsCut (s : Session) := do
  let ⟨hr⟩ ← refused s
  pure (PLift.up (rooms_cut (run (cutOps s)) hr))

def roomsRemoved (s : Session) := do
  let ⟨hr⟩ ← refused s
  pure (PLift.up (rooms_removed (run (cutOps s)) hr))

def openedEndpoint (s : Session) :=
  if h : check sodium (opened s) .opened [.inr (.request pkA pkB s.m1), .inl (.endpoint pkA staticA)] =
      some (.opened s.req.id c pkB "127.0.0.1:7447".toUTF8 [requestB.bytes]) then
    some (PLift.up (opened_endpoint sodium h))
  else none

def establishedEndpoint (s : Session) :=
  if h : check sodium (established s) .established
      [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
       .inr (.eph s.reply.id (sodium.suite.pub eA) eA), .inl (.endpoint pkA staticA)] =
      some (.established s.reply.id c pkB s.hash s.sendKey s.recvKey false) then
    some (PLift.up (established_endpoint sodium h))
  else none

instance : Fresh (Model F) := ⟨pure eA⟩
theorem freshPure : FreshPure := by intro s; rfl

def arrival (s : Session) := Recv.op s.req.id none "127.0.0.1:7447".toUTF8 0
def awaitingOps (s : Session) := before ++ myOps ++ [s.req,opened s,arrival s]
def unapprovedOps (s : Session) := [r,invitation] ++ myOps ++ [s.req,opened s,arrival s]

def answerTrusted (s : Session) :=
  if hm : (((react fam sodium : Model F (List Op)).run (run (awaitingOps s))).1).any
      (fun o => decide (o = s.reply)) = true then
    if hb : (decode s.reply.body : Option Connection.Body) = some (.connection s.m2) then
      some (PLift.up (answer_trusted ed25519 sodium freshPure (run (awaitingOps s)) s.reply s.m2
        (by obtain ⟨o,ho,he⟩ := List.any_eq_true.1 hm; exact (of_decide_eq_true he) ▸ ho) hb))
    else none
  else none

def resendTrusted (s : Session) :=
  let addr := "127.0.0.1:7447".toUTF8
  let q := Send.op addr s.reply
  if hm : (((onArrival none addr s.req 1 : Model F (List Op)).run (run (activeOps s))).1).any
      (fun o => decide (o = q)) = true then
    some (PLift.up (resend_trusted (run (activeOps s)) addr s.req 1 q addr
      (by obtain ⟨o,ho,he⟩ := List.any_eq_true.1 hm; exact (of_decide_eq_true he) ▸ ho)
      (decode_encode _)))
  else none

def bareJoin (s : Session) :=
  if hm : (((react fam sodium : Model F (List Op)).run (run (unapprovedOps s))).1).any
      (fun o => decide (o = requestB)) = true then
    if hs : (fam.room requestB).isSome = true then
      some (PLift.up (bare_takes_only_join ed25519 sodium (run (unapprovedOps s)) requestB
        (by obtain ⟨o,ho,he⟩ := List.any_eq_true.1 hm; exact (of_decide_eq_true he) ▸ ho) hs))
    else none
  else none

def invite : Community.Invite := ⟨c, invitation.id, pkA, ["127.0.0.1:7447".toUTF8], (sha256 "vacuity-invitation".toUTF8)⟩
def joinTravels := Community.joinOps_travels ed25519 invite (sha256 "vacuity-carol".toUTF8) "Carol".toUTF8 pkB
def stopLocal := Community.stopWaiting_local ed25519 requestB.id
def foundTravels := Community.found_travels ed25519 (DB.empty : DB Community.Fact)
  (sha256 "vacuity-founder".toUTF8) "New test community".toUTF8 "Founder".toUTF8 1
  (Bytes.digest "vacuity-content".toUTF8) (Bytes.fit 32 eA) (Bytes.fit 32 staticA)

/-! ## A session's end forgets its keys (`Connection.close_forgets` and the purge laws)

The real Noise session above, with its ephemeral and transport keys stored
(`eph`, `established`); its close step purges the connection and the request
it answers. -/

instance : Fresh (HeldM F) := ⟨pure eA⟩

/-- What the close step purges for this session (`closing`). -/
def closeIds (s : Session) : List Id := s.reply.id :: s.reply.reqs
def heldOf (s : Session) : Held F := { db := run (activeOps s) }
/-- The running node's driver over this store: the family's own hooks, so
its `closing` is the one that runs. -/
def nodeSync : Sync F (HeldM F) := { fam, hooks := Connection.hooks fam sodium "127.0.0.1:7447".toUTF8 }
def purged (s : Session) := drainS fam 500 (purgeS fam (closeIds s) (run (activeOps s)))
def closed (s : Session) := ((Node.endSession nodeSync s.reply.id : HeldM F Effects) (heldOf s)).2

def purgeForgets (s : Session) :=
  some (PLift.up (purge_forgets (C := ed25519) (K := sodium) (runInv (activeOps s)) (closeIds s) 500))
def forgetStays (s : Session) :=
  some (PLift.up (forget_stays (C := ed25519) (K := sodium)
    (inv_drainS (purge_inv (runInv (activeOps s)) (closeIds s)) 500)
    (purge_uncited (runInv (activeOps s)) (closeIds s) 500) [message.id] 500))
def closeForgets (s : Session) :=
  some (PLift.up (close_forgets (C := ed25519) (K := sodium) nodeSync rfl rfl (heldOf s)
    (runInv (activeOps s)) s.reply.id))
def retiredComplete (s : Session) :=
  let row := ((established s).id, Fact.established s.reply.id c pkB s.hash s.sendKey s.recvKey false)
  if hy : ((rows Connection.established.all [] : Model F _).run (run (activeOps s))).1.any
      (fun r => decide (r = row)) = true then
    some (PLift.up (retired_complete (run (activeOps s))
      (by obtain ⟨r, hr, he⟩ := List.any_eq_true.1 hy; exact (of_decide_eq_true he) ▸ hr)))
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  let some s := session | IO.eprintln "Could not construct real Noise session"; return 1
  for (label,ok) in [("projection",(projection s).isSome),("node connect",(nodeConnect s).isSome),
      ("node members",(nodeMembers s).isSome),("node recipients",(nodeRecipients s).isSome),
      ("node settles",(nodeSettles s).isSome),("wire kinds",(wireKinds s).isSome),("local kinds",(localKinds s).isSome),
      ("me node",(meNode s).isSome),("live trust",(trustsLive s).isSome),
      ("rooms trusted",(roomsTrusted s).isSome),("rooms complete",(roomsComplete s).isSome),
      ("rooms cut",(roomsCut s).isSome),("rooms removed",(roomsRemoved s).isSome),
      ("rooms model",(roomsModel s).isSome),("opened endpoint",(openedEndpoint s).isSome),
      ("established endpoint",(establishedEndpoint s).isSome),
      ("trusted answer",(answerTrusted s).isSome),("trusted resend",(resendTrusted s).isSome),
      ("bare path join",(bareJoin s).isSome),("purge forgets",(purgeForgets s).isSome),
      ("forgotten stays",(forgetStays s).isSome),("close forgets",(closeForgets s).isSome),
      ("established kept open or retired",(retiredComplete s).isSome)] do
    t.ok label ok
  let keyRows := [(established s).id, (eph s).id]
  t.ok "the session's key rows are stored before it ends"
    (keyRows.all fun y => ((run (activeOps s)).ops y).isSome)
  t.ok "the close step, as the node runs it, deletes them"
    (keyRows.all fun y => ((closed s).db.ops y).isNone)
  t.ok "the purge of the closing ids deletes them" (keyRows.all fun y => ((purged s).ops y).isNone)
  t.ok "a later purge leaves them gone"
    (keyRows.all fun y => ((drainS fam 500 (purgeS fam [message.id] (purged s))).ops y).isNone)
  t.ok "the community's ops stay" (((closed s).db.ops message.id).isSome)
  t.ok "active session syncs real community" ((roomsV s.reply.id).eval (run (activeOps s)) == [Room.sync c])
  t.ok "removed peer gets only actual removal notice" ((roomsV s.reply.id).eval (run (cutOps s)) == [Room.notice c removeB.id])
  t.ok "node admits Bob before removal" (((Community.allowPeer c pkB).liftL : View F Bool).eval (run (activeOps s)))
  t.ok "node refuses Bob after removal" (!((Community.allowPeer c pkB).liftL : View F Bool).eval (run (cutOps s)))
  t.ok "different node/device keys" (pkA != alice.pk && pkB != bob.pk)
  let joining := (Community.joinOps invite (sha256 "vacuity-carol".toUTF8) "Carol".toUTF8 pkB).ops
  t.ok "concrete invite has valid field sizes" (decide invite.Valid)
  t.ok "join sends exactly one op and retains local ops" ((joining.filter (Community.family ed25519).shared).length == 1 && joining.length > 1)
  t.ok "unapproved request gets no connection reply"
    (!(((react fam sodium : Model F (List Op)).run (run (unapprovedOps s))).1.any (fun o => o.kind == 35)))
  t.ok "removed peer replay gets no send courier"
    (!(((onArrival none "127.0.0.1:7447".toUTF8 s.req 2 : Model F (List Op)).run (run (cutOps s))).1.any (fun o => o.kind == 37)))
  t.finish "connection premises (real Noise session and removal)"

end Vacuity.IdentityConnection
