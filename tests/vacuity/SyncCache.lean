import tests.vacuity.SyncMore
import ops.sync.NoticeLaws

namespace Vacuity.SyncCache
open Engine Engine.Sync Vacuity.Network Vacuity.SyncMore
attribute [local instance] byteArray_lawfulBEq

theorem heldInv : Inv fam held.db := inv_drain fam (inv_ingest inv_empty msg) _
def boot : Node := Node.boot fam (held.db.stored.filterMap held.db.ops) 0

theorem messageIndexed : (keyOf fam msg, msg.id) ∈ boot.ix.items room :=
  (cached_items fam heldInv bootCache room _).2 ⟨msg, stored, rfl, rfl⟩

theorem indexAnswers : heldIn fam held.db room msg.id = true ↔
    ∃ a ∈ boot.ix.items room, a.2 = msg.id := heldIn_index fam heldInv bootCache room msg.id

-- The filed path actually sends an advertisement; all cache/invariant
-- premises are constructed for the nonempty held store.
theorem shownAfterFile : Keeps fam boot.ix conn held
    ((conn.filed fam cfg [msg.id] : HeldM Unit Step) held) :=
  (have_shown fam cfg heldInv bootCache (open_keeps fam (s := held.db) false [room] 0 0).1).2.2 [msg.id]

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

def snapConn : Conn := { conn with snaps := [((room, 1), [(keyOf fam msg, msg.id)])] }
theorem snapshotIn : SnapsIn boot.ix snapConn := by
  intro p hp a ha
  obtain rfl := List.mem_singleton.mp hp
  obtain rfl := List.mem_singleton.mp ha
  exact messageIndexed

theorem snapshotKept : SnapsIn (boot.write (setup.sync .a) [msg] held).1.1.ix snapConn :=
  write_snaps (setup.sync .a) snapshotIn [msg] held

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
  room_independent cfg ix roundConn room 100 0 rfl (by simp [roundConn, conn, Conn.open]) rfl

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
  [(⟨0, 1⟩, "remote-message-id".toUTF8)] 100 (by simp [conn, Conn.open]) rfl

theorem retryBound : (retried ((asking.work fam cfg ix 1500 : HeldM Unit Step) held).1.send).length ≤ cfg.maxIds :=
  work_retry_bounded fam cfg ix asking 1500 held

end Vacuity.SyncCache
