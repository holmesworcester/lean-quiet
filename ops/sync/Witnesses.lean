/-
Non-vacuity for secrecy and the liveness histories. The witnesses execute
filed and recv on held stores, with actual encoded messages.
-/
import ops.sync.SecrecyLaws
import ops.sync.TimeLaws

namespace Engine.Sync

/-- A real stored leaf is advertised, inhabiting both secrecy laws' premise. -/
theorem secrecy_runs (r : Id) :
    ∃ (c : Conn) (h : Held Unit) (ids : List Id),
      (Msg.hold r ids).op ∈ ((c.filed (oneRoom r) {} [(Op.make 1 [] .empty).id] : HeldM Unit Step) h).1.send ∧
      (Op.make 1 [] .empty).id ∈ ids := by
  let o := Op.make 1 [] .empty
  let c := (Conn.open false [r] 0 0).conn
  let h := turnH (oneRoom r) [o] {}
  have stored : h.db.ops o.id = some o := turnH_one (oneRoom r) o {} rfl
  obtain ⟨ids, hs, hi⟩ := filed_offers (oneRoom r) {} c [o.id] h o.id o r
    (by simp) stored rfl (by simp [c, Conn.open, Conn.shows, oneRoom, Family.room, has])
    (by simp [c, Conn.open]) (by simp [c, Conn.open]) (by decide)
  exact ⟨c, h, ids, hs, hi⟩

/-- Histories with an actual empty-have arrival each millisecond satisfy
all scheduler and delivery premises of live_stays, with live = 3. -/
theorem live_runs {F : Type} (fam : Family F) :
    let cfg : Config := { live := 3 }
    let c := fun now => (((Conn.open false [] 0 0).conn.recv fam cfg {}
      (Msg.hold .empty []).op.bytes now : HeldM F Step) {}).1.conn
    ∀ now, (((c now).tick fam cfg {} now : HeldM F Step) ({} : Held F)).1.drop = false := by
  intro cfg c
  have heard (now : Nat) : (c now).heard = now := by
    simp [c, Conn.open, Conn.recv, Op.decode_bytes, ofOp_hold, Conn.onHold, has]
  have sched : ∀ now, cfg.live < now → ∃ t, True ∧ t + cfg.live / 3 ≤ now ∧ now ≤ t + 2 * (cfg.live / 3) := by
    intro now hn
    refine ⟨now - 1, trivial, ?_, ?_⟩ <;> dsimp [cfg] at * <;> omega
  have deliver : ∀ now t, True → t + cfg.live / 3 ≤ now →
      (((c t).tick fam cfg {} t : HeldM F Step) {}).1.send = [] → (c t).sent ≤ (c now).heard := by
    intro now t _ _ _
    simp [c, Conn.open, Conn.recv, Op.decode_bytes, ofOp_hold, Conn.onHold, has]
  have both := live_stays fam cfg (fun _ => {}) (fun _ => {}) c c (fun _ => {}) (fun _ => {})
    (fun _ => True) (fun _ => True) (by decide) sched sched
    (fun now t ht old => ⟨deliver now t ht old, fun _ => by rw [heard]; dsimp [cfg] at old; omega⟩)
    (fun now t ht old => ⟨deliver now t ht old, fun _ => by rw [heard]; dsimp [cfg] at old; omega⟩)
  exact fun now => (both now).1
end Engine.Sync
