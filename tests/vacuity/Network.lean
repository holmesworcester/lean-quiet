import ops.sync.Witnesses
import ops.sync.ConnLaws

/-! Concrete sync fixtures. The payload and room are synthetic. The running
Conn/Node functions are exercised on the one-room Unit family, not the
Community crypto/membership family. This does not certify membership or seals. -/
namespace Vacuity.Network
open Engine Engine.Sync
attribute [local instance] byteArray_lawfulBEq

def room : Id := "vacuity/community/alice-bob".toUTF8
def sessionId : Id := "vacuity/session/alice-bob".toUTF8
def msg : Op := Op.make 1 [] "Alice: hello Bob".toUTF8
def fam : Family Unit := oneRoom room
def cfg : Config := {}
def conn : Conn := (Conn.open false [room] 0 0).conn
def held : Held Unit := turnH fam [msg] {}

theorem stored : held.db.ops msg.id = some msg := turnH_one fam msg {} rfl

theorem shown : conn.shows fam msg = true := by
  simp [conn, Conn.open, Conn.shows, fam, oneRoom, Family.room, has]

/-- An actual nonempty filed advertisement; its membership premise is proved. -/
theorem filedWitness : ∃ ids,
    (Msg.hold room ids).op ∈ ((conn.filed fam cfg [msg.id] : HeldM Unit Step) held).1.send ∧
    msg.id ∈ ids := by
  exact filed_offers fam cfg conn [msg.id] held msg.id msg room
    (by simp) stored rfl shown
    (by simp [conn, Conn.open]) (by simp [conn, Conn.open]) (by decide)

theorem shared : ∃ ids,
    (Msg.hold room ids).op ∈ ((conn.filed fam cfg [msg.id] : HeldM Unit Step) held).1.send ∧
    msg.id ∈ ids ∧ ∃ o, held.db.ops msg.id = some o ∧ (fam.room o).isSome = true := by
  obtain ⟨ids, hm, hi⟩ := filedWitness
  exact ⟨ids, hm, hi, offer_shared fam cfg conn [msg.id] held room msg.id ids
    (List.mem_append_left _ hm) hi⟩

theorem storedOffer : ∃ ids,
    (Msg.hold room ids).op ∈ ((conn.filed fam cfg [msg.id] : HeldM Unit Step) held).1.send ∧
    msg.id ∈ ids ∧ ∃ o, held.db.ops msg.id = some o := by
  obtain ⟨ids, hm, hi⟩ := filedWitness
  exact ⟨ids, hm, hi, offer_stored fam cfg conn [msg.id] held room msg.id ids
    (List.mem_append_left _ hm) hi⟩

/-- Nonempty wanted queue, actually stored and shown. -/
def queued : Conn := { conn with owed := [msg.id], owing := ({} : Std.HashSet Id).insert msg.id }

theorem servesHead : msg ∈ ((queued.serveOwed fam cfg 1024 [] : HeldM Unit _) held).1.2.2 :=
  serveOwed_head fam cfg queued 1024 held msg.id [] msg (by decide) rfl stored shown

theorem servedShown : queued.shows fam msg = true ∧
    ∃ i, (i ∈ queued.owed ∨ (i ∈ ([] : List Id) ∧ queued.owing.contains i = true)) ∧ held.db.ops i = some msg :=
  serveOwed_shown fam cfg queued 1024 [] held msg (Or.inr servesHead)

theorem servesFresh : msg ∈ ((queued.serveOwed fam cfg 0 [msg.id] : HeldM Unit _) held).1.2.1 :=
  serveOwed_hot fam cfg queued 0 [msg.id] held msg.id msg (by simp)
    (by simp [queued]) stored shown

theorem drains : (Nat.repeat (fun c => ((c.serveOwed fam cfg 1024 [] : HeldM Unit _) held).1.1)
    queued.owed.length queued).owed = [] := owed_within fam cfg 1024 held (by decide) queued

theorem fifo : ∃ pre, queued.owed = pre ++ ((queued.serveOwed fam cfg 1024 [] : HeldM Unit _) held).1.1.owed :=
  serveOwed_fifo fam cfg queued 1024 held

/-- A zero budget does not serve a queued message (urgent sends are separate). -/
theorem zeroBudget : ((queued.serveOwed fam cfg 0 [] : HeldM Unit _) held).1.2.2 = [] := by
  rw [(serveOwed_run fam cfg queued 0 [] held).1]
  rfl

/-- Real wire bytes for a nonempty have satisfy both decoding premises. -/
theorem havePremises : Op.decode (Msg.hold room [msg.id]).op.bytes = some (Msg.hold room [msg.id]).op ∧
    Msg.ofOp (Msg.hold room [msg.id]).op = some (.hold room [msg.id]) :=
  hold_reply_local_premises room [msg.id]

-- Silence threshold checks exercise both outcomes of the exact iff.
theorem timesOut : ((conn.tick fam cfg {} 90001 : HeldM Unit Step) held).1.drop = true :=
  (drop_iff_silent fam cfg {} conn 90001 held).2 (by decide)

theorem deadlineStillLive : ((conn.tick fam cfg {} 90000 : HeldM Unit Step) held).1.drop = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have impossible := (drop_iff_silent fam cfg {} conn 90000 held).1 h
  exact (by decide : ¬ conn.heard + cfg.live < 90000) impossible

/-- Known existing non-vacuity witnesses run actual keepalives and delivery;
instantiate their room, session id and family here. -/
theorem keepalive :
    (((Conn.open false [] 0 0).conn.tick fam cfg {} 30000 : HeldM Unit Step) {}).1.send =
      [(Msg.hold .empty []).op] := keepalive_runs fam cfg false

theorem streamDelivery : ∃ w,
    World.Steps ⟨oneRoom room, {}, fun _ _ => [room]⟩ (World.empty (oneRoom room)) w ∧
    (w.peer .b).held.db.ops (Op.make 1 [] .empty).id = some (Op.make 1 [] .empty) :=
  stream_delivers_runs room sessionId

theorem streamOffer : ∃ w ps l,
    World.Steps ⟨oneRoom room, {}, fun _ _ => [room]⟩ (World.empty (oneRoom room)) w ∧
    ⟨(w.peer .b).addr, plainFrame sessionId ps⟩ ∈ w.net ∧
    (Msg.hold room l).op.bytes ∈ ps ∧ (Op.make 1 [] .empty).id ∈ l :=
  stream_offered_runs room sessionId

-- Nonempty output makes recv_send's universal membership premise meaningful.
theorem helloSends : ((conn.recv fam cfg {} (Msg.hello 0).op.bytes 100 : Model Unit Step).run held.db).1.send =
    [(Msg.hello 0).op] := by
  simp [Conn.recv, Op.decode_bytes, Msg.ofOp, Msg.op, kRbsr, Codec.decode_encode, conn, Conn.open, Model.run_pure]

theorem receiveSendable : Sendable fam conn (Msg.hello 0).op :=
  recv_send fam cfg {} conn (Msg.hello 0).op.bytes 100 held.db _ (by rw [helloSends]; simp)

theorem messageTaken : ((conn.recv fam cfg {} msg.bytes 100 : Model Unit Step).run held.db).1.take = [msg] := by
  simp [Conn.recv, Op.decode_bytes, msg, Msg.ofOp, isWire, kRbsr, kHave, kWant,
    Conn.shows, conn, Conn.open, fam, oneRoom, Family.room, has, Model.run_pure]

theorem receiveTakeable : Takeable fam conn msg :=
  recv_take fam cfg {} conn msg.bytes 100 held.db _ (by rw [messageTaken]; simp)

-- Authorize a real requested id using the shown-room index, then queue it.
def ix : Index := ⟨[(room, [(⟨0, 0⟩, msg.id)])]⟩
theorem authorized : msg.id ∈ authorize ix conn [msg.id] := by
  simp [authorize, ix, Index.items, conn, Conn.open]

theorem wantQueued : msg.id ∈ (conn.onWant cfg ix [msg.id]).conn.owed := by
  have h := onWant_all cfg ix conn [msg.id] (by decide) (by decide) msg.id authorized
  rcases h with h | h
  · simp [conn, Conn.open] at h
  · exact h

theorem wantAuthorized : msg.id ∈ conn.owed ∨
    (msg.id ∈ [msg.id] ∧ ∃ r ∈ conn.rooms, ∃ a ∈ ix.items r, a.2 = msg.id) :=
  onWant_authorized cfg ix conn [msg.id] msg.id wantQueued

theorem wantOrder : ∃ add, (conn.onWant cfg ix [msg.id]).conn.owed = conn.owed ++ add :=
  onWant_order cfg ix conn [msg.id]

-- Remove the room permission: the same indexed id is no longer queued.
theorem noRoomNoQueue : (({ conn with rooms := [] } : Conn).onWant cfg ix [msg.id]).conn.owed = [] := by
  simp [Conn.onWant, authorize, conn, Conn.open, cfg]

-- A local secret exists in one store and is absent from the other. A
-- malicious have names that secret's actual op id in the shown room.
def localFamily : Family Unit :=
  { validate := fun _ _ => some (), keys := fun _ => [],
    scope := fun o => if o.kind = 1 then .shared room else .local }
def secret : Op := Op.make 2 [] "synthetic local session secret".toUTF8
def secretHeld : Held Unit := { db := DB.empty.putOp secret, log := [secret] }

theorem secretNotShared : localFamily.room secret = none := by
  simp [localFamily, Family.room, secret]

theorem localStoresAgree : RoomsAgree localFamily conn.rooms secretHeld.db ({} : Held Unit).db := by
  intro x o r _ hr
  constructor
  · intro ho
    simp only [secretHeld, DB.putOp, DB.empty] at ho
    split at ho
    · cases ho
      rw [secretNotShared] at hr
      cases hr
    · cases ho
  · intro ho
    cases ho

theorem hiddenProbe :
    ((conn.recv localFamily cfg {} (Msg.hold room [secret.id]).op.bytes 100 : HeldM Unit Step) secretHeld).1 =
      ((conn.recv localFamily cfg {} (Msg.hold room [secret.id]).op.bytes 100 : HeldM Unit Step) {}).1 ∧
    ((conn.recv localFamily cfg {} (Msg.hold room [secret.id]).op.bytes 100 : HeldM Unit Step) secretHeld).2 = secretHeld ∧
    ((conn.recv localFamily cfg {} (Msg.hold room [secret.id]).op.bytes 100 : HeldM Unit Step) {}).2 = {} :=
  hold_reply_local localFamily cfg {} conn 100 (Op.decode_bytes _) (ofOp_hold _ _) localStoresAgree

-- A queued message in a room the connection no longer carries cannot be served.
theorem revokedNotServed : (({ queued with rooms := [] } : Conn).serveOwed fam cfg 1024 [] : HeldM Unit _) held |>.1.2.2 = [] := by
  rw [(serveOwed_run fam cfg { queued with rooms := [] } 1024 [] held).1]
  simp [Conn.owedAfter, Conn.hotOf, queued, serve_cons, stored, Conn.shows, fam, oneRoom, Family.room, has, serve_nil]

theorem filedModelAgrees :
    ((conn.filed fam cfg [msg.id] : Model Unit Step).run held.db).1.send =
    ((conn.filed fam cfg [msg.id] : HeldM Unit Step) held).1.send := by
  simp [Conn.filed, List.forIn_cons, List.forIn_nil, Model.run_bind, Model.run_pure,
    HeldM.bind_apply, HeldM.pure_apply, conn, Conn.open, stored,
    HeldM.getOp_apply, Conn.shows, fam, oneRoom, Family.room, has]

theorem filedWire : ∃ ids,
    (Msg.hold room ids).op ∈ ((conn.filed fam cfg [msg.id] : Model Unit Step).run held.db).1.send ∧
    msg.id ∈ ids ∧ isWire (Msg.hold room ids).op.kind = true := by
  obtain ⟨ids, hm, hi⟩ := filedWitness
  rw [← filedModelAgrees] at hm
  exact ⟨ids, hm, hi, (filed_send fam cfg conn [msg.id] held.db).1 _ hm⟩

-- Actual keepalive output inhabits tick_send's output-membership premise.
theorem tickWire : isWire (Msg.hold .empty []).op.kind = true := by
  apply (tick_send fam cfg {} (Conn.open false [] 0 0).conn 30000 ({} : Held Unit).db).1
  have h : (((Conn.open false [] 0 0).conn.tick fam cfg {} 30000 : Model Unit Step).run
      ({} : Held Unit).db).1.send = [(Msg.hold .empty []).op] := keepalive
  rw [h]
  simp

-- The existing live_runs witness constructs actual received keepalives and
-- discharges both delivery and scheduler premises of live_stays for all times.
theorem keepaliveHistory :
    let config : Config := { live := 3 }
    let c := fun now => (((Conn.open false [] 0 0).conn.recv fam config {}
      (Msg.hold .empty []).op.bytes now : HeldM Unit Step) {}).1.conn
    ∀ now, (((c now).tick fam config {} now : HeldM Unit Step) {}).1.drop = false :=
  live_runs fam

end Vacuity.Network
