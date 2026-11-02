import tests.vacuity.SyncMore
import engine.sync.NoticeLaws
import engine.sync.EventLaws

namespace Vacuity.SyncCache
open Engine Engine.Sync Vacuity.Network Vacuity.SyncMore
attribute [local instance] byteArray_lawfulBEq

theorem heldInv : Inv fam held.db := inv_turnCapped inv_empty drainCap [msg]
def boot : Node := Node.boot fam (held.db.stored.filterMap held.db.ops) 0

theorem messageIndexed : (keyOf fam msg, msg.id) ∈ boot.ix.items room :=
  (cached_items fam heldInv bootCache room _).2 ⟨msg, stored, rfl, rfl⟩

theorem indexAnswers : heldIn fam held.db room msg.id = true ↔
    ∃ a ∈ boot.ix.items room, a.2 = msg.id := heldIn_index fam heldInv bootCache room msg.id

-- The filed path actually sends an advertisement; all cache/invariant
-- premises are constructed for the nonempty held store.
theorem shownAfterFile : Keeps fam conn held
    ((conn.filed fam cfg [msg.id] : HeldM Unit Step) held) :=
  (have_shown fam cfg heldInv bootCache conn).2.2 [msg.id]

theorem writeCache :
    Inv (setup.sync .a).fam ((Node.boot fam [] 0).write (setup.sync .a) [msg] ({} : Held Unit)).2.db ∧
    Cached (setup.sync .a).fam ((Node.boot fam [] 0).write (setup.sync .a) [msg] ({} : Held Unit)).1.1
      ((Node.boot fam [] 0).write (setup.sync .a) [msg] ({} : Held Unit)).2.db :=
  write_cached (setup.sync .a) [msg] inv_empty (boot_cached fam DB.empty 0)

-- Purge the actual shared op: shared bytes are retained, so the cached
-- shared index must stay correct. Local deletion is covered by closeErases.
theorem purgeCache : Inv fam ((Turn.purge fam [msg.id] true : HeldM Unit Unit) held).2.db ∧
    Cached fam boot ((Turn.purge fam [msg.id] true : HeldM Unit Unit) held).2.db :=
  purge_cached fam [msg.id] true heldInv bootCache

-- A write turn keeps the indexed message: live answers read it after.
theorem indexKept : (keyOf fam msg, msg.id) ∈ (boot.write (setup.sync .a) [msg] held).1.1.ix.items room :=
  write_items (setup.sync .a) boot [msg] held room _ messageIndexed

-- Notice carries an actual stored leaf and no synchronized room.
def noticeConn : Conn := { conn with rooms := [], notices := [(room, msg.id)] }
theorem closureFits : ClosureWithin fam held.db.ops room msg.id cfg.walk := by
  refine ⟨[msg.id], by decide, ?_⟩
  intro y hy
  induction hy with
  | refl => simp
  | @step y o z _ hg _ hz ih =>
    obtain rfl := List.mem_singleton.mp ih
    rw [stored] at hg
    cases hg
    cases hz

theorem noticesSent : Gives fam held.db noticeConn room msg.id
    ((noticeConn.filedGive fam cfg [] : Model Unit Step).run held.db).1 ∧
    (((noticeConn.tick fam cfg {} 100 : Model Unit Step).run held.db).1.drop = false →
      Gives fam held.db noticeConn room msg.id ((noticeConn.tickGive fam cfg {} 100 : Model Unit Step).run held.db).1) :=
  notice_sent fam cfg {} held.db heldInv.key noticeConn [] 100 room msg.id (by simp [noticeConn])
    rfl (by intro r h; simpa [noticeConn] using h) closureFits

theorem actualNotice : msg ∈ ((noticeConn.filedGive fam cfg [] : Model Unit Step).run held.db).1.send :=
  noticesSent.1.2.2 msg.id msg .refl stored rfl (by simp [noticeConn, conn, Conn.open])

theorem onlyNotice : isWire msg.kind = true ∨ NoticeOp fam held.db noticeConn msg :=
  (notice_send fam cfg {} held.db noticeConn [] 100 _ (by simp)).1 msg actualNotice

def givenConn : Conn := { noticeConn with given := [msg.id] }
theorem noticeOnce :
    (∀ o ∈ ((givenConn.filedGive fam cfg [] : Model Unit Step).run held.db).1.send, isWire o.kind = true) ∧
    (∀ o ∈ ((givenConn.tickGive fam cfg {} 100 : Model Unit Step).run held.db).1.send, isWire o.kind = true) :=
  notice_once fam cfg {} held.db givenConn [] 100 (by
    intro p hp
    obtain rfl := List.mem_singleton.mp hp
    simp [givenConn, has])

theorem noticesNoProbe :
    ((conn.carry [.notice room msg.id] |>.recv fam cfg {} (Msg.hold room [msg.id]).op.bytes 100 : Model Unit Step).run held.db).1.send = [] ∧
    ((conn.carry [.notice room msg.id] |>.recv fam cfg {} (Msg.hold room [msg.id]).op.bytes 100 : Model Unit Step).run held.db).1.take = [] ∧
    ((conn.carry [.notice room msg.id] |>.recv fam cfg {} (Msg.hold room [msg.id]).op.bytes 100 : Model Unit Step).run held.db).2 = held.db :=
  notice_no_holds fam cfg {} conn [.notice room msg.id] room [msg.id] _ 100 held.db
    (Op.decode_bytes _) (ofOp_hold _ _) (by simp)

theorem noticeClosure : msg ∈ ((closureOps fam room cfg.walk [msg.id] [] : Model Unit (List Op)).run held.db).1 :=
  (closure fam held.db room msg.id cfg.walk).2 closureFits _ _ .refl stored rfl

def roundConn : Conn := { conn with peerFloor := some 0 }
theorem startsRoom : (Msg.rbsr room (roundConn.round + 1)
    ((window (max roundConn.floor 0)).map (opening Prod.fst Prod.snd sha256 cfg.params (ix.items room)))).op ∈
    (roundConn.start cfg ix 100).send :=
  room_independent cfg ix roundConn room 100 0 rfl (by simp [roundConn, conn, Conn.open])
    (by simp [Conn.due, Conn.roundedAt, roundConn, conn, Conn.open])

def refused : Conn := { conn with rooms := [] }
theorem refusesRound : refused.onRbsr cfg ix room 7 [.ids range [msg.id]] 100 =
    { conn := refused, send := [(Msg.rbsr room 7 []).op] } :=
  unshown_room_answered cfg ix refused room 7 100 [.ids range [msg.id]] rfl

theorem acceptsNewRound : (conn.onRbsr cfg ix room 7 [.ids range [msg.id]] 100).send.head? =
    some (Msg.rbsr room 7
      (([Claim.ids range [msg.id]].flatMap (answer Prod.fst Prod.snd sha256 cfg.params (ix.items room))).filterMap
        fun | .claim x => some x | _ => none)).op :=
  uncarried_room_answered cfg ix conn room 7 100 [.ids range [msg.id]]
    (by simp [conn, Conn.open, has]) rfl rfl

def answersIds := conn_answers_ids cfg ix conn room 7 range (ix.items room)
  [(⟨0, 1⟩, "remote-message-id".toUTF8)] 100 (by simp [conn, Conn.open]) rfl rfl

-- Event rounds on a session whose peers' floors are known: the dialer,
-- and the responder, each with the room shown and no round in it yet.
def dialerConn : Conn := { conn with dialer := true, peerFloor := some 0 }
def responderConn : Conn := { conn with peerFloor := some 0 }

theorem dueRoundOpens : (Msg.rbsr room (dialerConn.round + 1)
    ((window (max dialerConn.floor 0)).map (opening Prod.fst Prod.snd sha256 cfg.params (ix.items room)))).op ∈
    ((dialerConn.tick fam cfg ix 100 : HeldM Unit Step) held).1.send :=
  round_due fam cfg ix dialerConn room 100 0 held rfl rfl (by simp [dialerConn, conn, Conn.open])
    (by simp [dialerConn, conn, Conn.open, cfg]) (by simp [Conn.due, Conn.roundedAt, dialerConn, conn, Conn.open])

theorem responderAsks : (Msg.hold room []).op ∈ ((responderConn.tick fam cfg ix 100 : HeldM Unit Step) held).1.send :=
  responder_asks fam cfg ix responderConn room 100 0 held rfl rfl (by simp [responderConn, conn, Conn.open])
    (by simp [responderConn, conn, Conn.open, cfg]) (by simp [Conn.roundedAt, responderConn, conn, Conn.open])

/-- The same responder, the same tick: it asks (responderAsks) but opens
no round, even in the room it shows with none yet. -/
theorem responderOpensNone :
    (Msg.rbsr room (responderConn.round + 1) []).op ∉ ((responderConn.tick fam cfg ix 100 : HeldM Unit Step) held).1.send :=
  responder_opens_none fam cfg ix responderConn 100 held rfl room _ []

def askMakesDue :=
  ask_due fam cfg ix dialerConn room 100 200 held rfl (by simp [dialerConn, conn, Conn.open])
    (by simp [dialerConn, conn, Conn.open])

def joinRound :=
  join_round fam cfg ix ix dialerConn responderConn room 100 200 300 0 0 held held rfl rfl rfl rfl
    (by simp [dialerConn, conn, Conn.open]) (by simp [responderConn, conn, Conn.open])
    (by simp [Conn.roundedAt, responderConn, conn, Conn.open]) (by simp [dialerConn, conn, Conn.open])
    (by simp [responderConn, conn, Conn.open, cfg]) (by simp [cfg])

def shownDue := shown_due cfg { conn with rooms := [] } [room] room 100 (by simp)

-- The room's round opened at 50: none again before the safety period.
def quietConn : Conn := { dialerConn with rounded := [(room, 50)] }
theorem quietUntilSafety (k : Nat) (cs : List Claim) :
    (Msg.rbsr room k cs).op ∉ ((quietConn.tick fam cfg ix 100 : HeldM Unit Step) held).1.send :=
  no_round_before_safety fam cfg ix quietConn 100 held room 50 (by simp [Conn.roundedAt, quietConn])
    (by simp [cfg]) rfl k cs

theorem retryBound : (retried ((asking.work fam cfg ix 1500 : HeldM Unit Step) held).1.send).length ≤ cfg.maxIds :=
  work_retry_bounded fam cfg ix asking 1500 held

end Vacuity.SyncCache
