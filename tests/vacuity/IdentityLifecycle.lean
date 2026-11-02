import tests.vacuity.IdentityConnection
import app.Proofs

namespace Vacuity.IdentityLifecycle
open Engine Codec Tests Connection Vacuity.Identity Vacuity.IdentityConnection
open Community (ed25519)
set_option linter.defProp false

def addr := "127.0.0.1:7447".toUTF8
def givenOps (s : Session) := cutOps s ++ [arrival s,Given.op s.reply.id removeB.id]
def acceptanceRows := [((Community.sortOf (Community.Fact.accepted c alice.pk), (Community.accept c alice.pk).id),
  Community.Fact.accepted c alice.pk)]

theorem onlyCommunity (db : DB F)
    (ha : (eval db (Community.accepted.all.query [])).lefts = acceptanceRows)
    {c' d a : ByteArray} (hm : ((Community.mine c').liftL : View F _).eval db = some (d,a)) : c' = c := by
  by_cases hn : c' = c
  · exact hn
  exfalso
  have hx : ((Community.mine c').liftL : View F _).eval db = none := by
    change (((Community.pick c' (eval db (Community.joining.all.query [])).lefts
      (eval db (Community.accepted.all.query [])).lefts).bind
      (fun best => .pure (best.map fun (d,a,_) => (d,a)))).liftL : View F _).eval db = none
    rw [ha]
    simp only [acceptanceRows, Community.pick, if_neg (Ne.symm hn)]
    rfl
  rw [hx] at hm
  cases hm

def noticeThenCut (s : Session) :=
  let db := run (givenOps s)
  if ha : (eval db (Community.accepted.all.query [])).lefts = acceptanceRows then
    if hm : (meV c).eval db = some pkA then
      if hl : ((Community.allowPeer c pkA).liftL : View F Bool).eval db = true then
        if hp : peersOf (eval db (Connection.established.byConn.query [s.reply.id])) = [pkB] then
          if hr : ((Community.allowPeer c pkB).liftL : View F Bool).eval db = false then
            if ho : ((Community.removalsAt c pkB).liftL : View F (List Id)).eval db = [removeB.id] then
              if hg : (givenOn s.reply.id).eval db = [removeB.id] then
                some (PLift.up (notice_then_cut db (cid := s.reply.id) (by
                  intro c' me he
                  obtain ⟨d,a,hma⟩ := (meV_node db he).2
                  have hc := onlyCommunity db ha hma
                  subst c'
                  refine ⟨?_,?_,?_⟩
                  · intro me' he'; rw [hm] at he'; cases he'; exact hl
                  · intro peer he'; rw [hp,List.mem_singleton] at he'; subst peer; exact hr
                  · intro x hx
                    obtain ⟨peer,hp',hx⟩ := hx
                    rw [hp,List.mem_singleton] at hp'; subst peer
                    rw [ho,List.mem_singleton] at hx; subst x
                    rw [hg]; exact List.mem_singleton_self _)))
              else none
            else none
          else none
        else none
      else none
    else none
  else none

-- Every admitted device on Bob's node belongs to Bob: reduce the universal
-- premise to all stored verdicts, using Inv.sound to rule out hidden verdicts.
def bobOwned (db : DB F) (x : Id) : Bool :=
  match db.status x with
  | some (.valid (.inl (.admission c' u d e))) => decide ((c' = c ∧ e = pkB) → u = requestB.id ∧ d = bob.pk)
  | _ => true

theorem onlyBob (db : DB F) (hi : Inv fam db)
    (hb : db.stored.all (bobOwned db) = true)
    {x u d : Id} (hx : db.status x = some (.valid (.inl (.admission c u d pkB)))) :
    u = requestB.id ∧ d = bob.pk := by
  obtain ⟨o,fs,ho,_⟩ := spec_valid_inv (hi.sound x _ hx)
  have hs : x ∈ db.stored := (hi.stored x).2 (by rw [ho]; rfl)
  have hh := (List.all_eq_true.1 hb) x hs
  simp only [bobOwned,hx] at hh
  exact of_decide_eq_true hh (by simp)

def roomsCutNode (s : Session) :=
  let db := run (cutOps s)
  if hq : db.queue = [] then
    if hm : (meV c).eval db = some pkA then
      if hl : ((Community.allowPeer c pkA).liftL : View F Bool).eval db = true then
        if hp : peersOf (eval db (Connection.established.byConn.query [s.reply.id])) = [pkB] then
          if hr : db.status removeB.id = some (.valid (.inl (.removal c requestB.id c))) then
            if hb : db.stored.all (bobOwned db) = true then
              some (PLift.up (rooms_cut_node (runInv (cutOps s)) hq (cid := s.reply.id) (c := c)
                (by
                  intro me he; rw [hm] at he; cases he
                  exact (connect_iff_node (runInv (cutOps s)) hq c pkA).1 hl)
                (by
                  intro peer he; rw [hp,List.mem_singleton] at he; subst peer
                  refine ⟨requestB.id,(removed_node (runInv (cutOps s)) hq).2 ⟨removeB.id,c,hr⟩,?_⟩
                  intro u d had
                  obtain ⟨x,hx⟩ := (admitted_node (runInv (cutOps s)) hq).1 had
                  obtain ⟨hu,_⟩ := onlyBob db (runInv (cutOps s)) hb hx
                  subst u
                  exact ⟨pkB,(admitted_node (runInv (cutOps s)) hq).2 ⟨x,hx⟩⟩)))
            else none
          else none
        else none
      else none
    else none
  else none

def pendingInvite : Community.Invite := ⟨c,invitation.id,pkA,[addr],(sha256 "vacuity-invitation".toUTF8),false⟩
def pendingJoin := Community.joining pendingInvite requestB.id "Bob".toUTF8 bob.pk
def endpointB := Community.endpoint staticB
def acceptB := Community.accept c bob.pk
def localBob := [Community.secret (sha256 "vacuity-bob".toUTF8),acceptB,endpointB,pendingJoin]
def pendingOps (s : Session) := [r,invitation,requestB] ++ localBob ++ [s.req,Eph.op eB s.req.id]
def reconnectOps (s : Session) := before ++ localBob ++ [s.req,Eph.op eB s.req.id]
def joinRow := ((Community.sortOf (Community.Fact.joining c pkA [addr] requestB.id "Bob".toUTF8 bob.pk 0),pendingJoin.id),
  Community.Fact.joining c pkA [addr] requestB.id "Bob".toUTF8 bob.pk 0)

def unanswered (s : Session) (ops : List Op) (waiting : Bool) :
    Option (PLift (Unanswered sodium addr (run ops) pkB staticB c pkA requestB.id waiting)) :=
  if hh : ((requestOf sodium staticB pkA requestB.id ((rows request.byFrm [pkB] : Model F _).run (run ops)).1 : Model F _).run (run ops)).1 = some s.req.id then
    if hn : (eval (run ops) (connection.byRequest.query [s.req.id] (limit := some 0))).total = 0 then
      if hs : ((run ops).ops s.req.id).isSome = true then
        some ⟨by unfold Unanswered; rw [hh]; exact ⟨fun _ => hn,hs⟩⟩
      else none
    else none
  else none

def rejoinDials (s : Session) := do
  let db := run (pendingOps s)
  let ⟨hu⟩ ← unanswered s (pendingOps s) true
  if hk : ((endpoints : Model F _).run db).1 = [(pkB,staticB,endpointB.id)] then
    if hj : ((eval db (Community.joining.all.query [])).lefts).any (fun r => decide (r = joinRow)) = true then
      if hm : ((Community.mine c).liftL : View F _).eval db = some (bob.pk,acceptB.id) then
        if hn : (eval db (Community.admission.byDevice.query [c,bob.pk] (limit := some 0))).total = 0 then
          pure (PLift.up (rejoin_dials sodium addr 100 freshPure db hk
            (by obtain ⟨r,hr,he⟩ := List.any_eq_true.1 hj; exact (of_decide_eq_true he) ▸ hr) hm hn hu))
        else none
      else none
    else none
  else none

def reconnectDials (s : Session) := do
  let db := run (reconnectOps s)
  let ⟨hu⟩ ← unanswered s (reconnectOps s) false
  if hk : ((endpoints : Model F _).run db).1 = [(pkB,staticB,endpointB.id)] then
    if hj : ((eval db (Community.joining.all.query [])).lefts).any (fun r => decide (r = joinRow)) = true then
      if hm : ((Community.mine c).liftL : View F _).eval db = some (bob.pk,acceptB.id) then
        if hn : (eval db (Community.admission.byDevice.query [c,bob.pk] (limit := some 0))).total ≠ 0 then
          if hc : ((connectedTo pkA : Model F Bool).run db).1 = false then
            pure (PLift.up (reconnect_dials sodium addr 100 freshPure db hk
              (by obtain ⟨r,hr,he⟩ := List.any_eq_true.1 hj; exact (of_decide_eq_true he) ▸ hr) hm hn hc hu))
          else none
        else none
      else none
    else none
  else none

def removedGetsOnlyNotice (s : Session) := do
  let ⟨hl⟩ ← liveIn s
  let ⟨hr⟩ ← refused s
  pure (PLift.up (removed_gets_only_notice fam {} {} (run (cutOps s)) s.reply.id c
    (Sync.Conn.open false [c] 0 0).conn message.bytes [removeB.id] 100 0 false hl hr))

/-! ## A removal reaches a live session, over a whole entry point

Alice's node, on held data with the family's own hooks, runs one tick
(`Node.onTick`) from the store where Bob is removed and their session is
open. The trust rule refuses Bob there, so `removal_reaches_session`
says every payload sealed for the session may go: the tick's frame for
Bob, opened with the session's key, carries the removal and not Bob's
message. -/

/-- Fresh bytes on held data from a fixed tape: they leave the store as it is. -/
instance heldFresh : Fresh (Sync.HeldM F) := ⟨fun h => (sha256 "vacuity-frame-nonce".toUTF8, h)⟩
theorem heldFreshReads : Sync.Reads (Fresh.fresh : Sync.HeldM F ByteArray) := fun _ => rfl

def bobAddr := "127.0.0.1:7448".toUTF8
def syncA : Sync.Sync F (Sync.HeldM F) :=
  { fam, cfg := {}, hooks := hooks fam sodium addr, catalog := some (Sync.Catalog.held fam) }
theorem catalogReads : ∀ cat, syncA.catalog = some cat →
    Sync.Reads cat.ceiling ∧ ∀ i, Sync.Reads (cat.read i) := by
  intro cat hc
  cases hc
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩
theorem retryStoreReads : ∀ store, syncA.retryStore = some store →
    (∀ peer, Sync.Reads (store.load peer)) ∧ (∀ peer cursor, Sync.Reads (store.save peer cursor)) := by
  intro store hs
  cases hs

def heldCut (s : Session) : Sync.Held F := { log := cutOps s, db := run (cutOps s) }
def nodeA (s : Session) : Sync.Node :=
  { Sync.Node.boot fam (cutOps s) 0 with
    conns := [(s.reply.id, (Sync.Conn.open false [c] 0 0).conn)]
    addrs := [(s.reply.id, bobAddr)]
    managed := [s.reply.id] }
def tickA (s : Session) := ((nodeA s).onTick syncA 100).run (heldCut s)

/-- The tick's frames to Bob, opened with the session's key: the ops they carry. -/
def tickPayloads (s : Session) : List Op :=
  (tickA s).1.2.send.flatMap fun (a, p) =>
    if a == bobAddr && p[0]? == some Sync.sealedTag then
      match Frame.open sodium s.sendKey (p.extract 1 p.size) with
      | some (_, b) => ((decode b : Option (List ByteArray)).getD []).filterMap Op.decode
      | none => []
    else []

def removalReachesSession (s : Session) := do
  let ⟨hl⟩ ← liveIn s
  let ⟨hr⟩ ← refused s
  pure (PLift.up (And.intro (And.intro hl hr)
    (removal_reaches_session heldFreshReads syncA sodium addr rfl catalogReads retryStoreReads (.tick 100) (nodeA s) (heldCut s))))

def entryFresh (s : Session) :=
  PLift.up (Sync.entry_fresh (hooks_readOnly heldFreshReads syncA sodium addr rfl catalogReads retryStoreReads) (.tick 100) (nodeA s) (heldCut s))

def noticeStep (s : Session) :=
  (((Sync.Conn.open false [c] 0 0).conn.carry ((roomsV s.reply.id).eval (run (cutOps s)))).filedGive
    fam {} [removeB.id] : Model F Sync.Step).run (run (cutOps s))

def main : IO UInt32 := do
  let t ← Checks.new
  let some s := session | IO.eprintln "Could not construct real Noise session"; return 1
  t.ok "durable retry identity is the authenticated peer key"
    (((Connection.retryKey s.reply.id : Sync.HeldM F _).run (heldCut s)).1 == some pkB)
  t.ok "unknown session has no durable retry identity"
    (((Connection.retryKey "unknown-session".toUTF8 : Sync.HeldM F _).run (heldCut s)).1.isNone)
  t.ok "rooms cut at combined node" (roomsCutNode s).isSome
  t.ok "removed peer only receives notice" (removedGetsOnlyNotice s).isSome
  t.ok "whole tick: trust rule refuses Bob where it starts" (removalReachesSession s).isSome
  have _ := entryFresh s
  t.ok "whole tick seals a frame for Bob's session"
    ((tickA s).1.2.send.any fun (a, p) => a == bobAddr && p[0]? == some Sync.sealedTag)
  t.ok "whole tick's frame carries the removal" ((tickPayloads s).any (·.id == removeB.id))
  t.ok "whole tick's frame excludes Bob's message" (!(tickPayloads s).any (·.id == message.id))
  let entries := Sync.Catalog.shared fam (heldCut s)
  let atMessage : Sync.Sweep := { after := entries.idxOf message, high := entries.length, active := true }
  let retryNode := { nodeA s with sweeps := [(s.reply.id, atMessage)] }
  let retry := (retryNode.sweep syncA s.reply.id).run (heldCut s)
  t.ok "catalog retry rechecks removal before emitting an otherwise retained message"
    (entries.contains message && retry.1.2.send.isEmpty && retry.1.2.serve.isEmpty &&
      retry.1.1.sweeps.any (fun p => p.1 == s.reply.id && p.2.after == atMessage.after + 1))
  t.ok "notice then cut" (noticeThenCut s).isSome
  t.ok "pending join dials" (rejoinDials s).isSome
  t.ok "admitted node reconnects" (reconnectDials s).isSome
  t.ok "given notice leaves no rooms" ((roomsV s.reply.id).eval (run (givenOps s)) == [])
  t.ok "retired connection is actual established session" (((retired : Model F _).run (run (givenOps s))).1.contains s.reply.id)
  t.ok "notice sends actual removal" ((noticeStep s).1.send.any (fun o => o.id == removeB.id))
  t.ok "notice excludes Bob message" (!((noticeStep s).1.send.any (fun o => o.id == message.id)))
  t.ok "removed peer message is not taken"
    ((((Sync.Conn.open false [c] 0 0).conn.carry ((roomsV s.reply.id).eval (run (cutOps s)))).recv
      fam {} {} message.bytes 100 : Model F Sync.Step).run (run (cutOps s))).1.take.isEmpty
  t.ok "retry actually sends to invite hint"
    ((((dial sodium addr 100 : Model F (List Op)).run (run (pendingOps s))).1).any
      (fun o => o.kind == 37 && (decode o.body : Option Connection.Body) == some (.send addr)))
  t.finish "connection lifecycle concrete premises"

end Vacuity.IdentityLifecycle
