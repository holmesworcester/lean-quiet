/-
The running clock's deadlines: patience begins at the latest arrival or
local round; responders additionally have a silence lease. All times
are plain logical milliseconds, so a runner may later subtract pauses.
-/
import ops.sync.ServeLaws

namespace Engine.Sync

variable {F : Type} (fam : Family F) (cfg : Config)

theorem tick_drop_iff (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.drop = true ↔
      (c.waiting = true ∧ c.waitStart + cfg.patience < now) ∨
      (c.dialer = false ∧ c.heard + cfg.lease < now) := by
  unfold Conn.tick
  split
  · simp only [HeldM.pure_apply, Conn.expired, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq] at *
    simp_all
  · simp only [HeldM.bind_apply, HeldM.pure_apply, Conn.finish]
    have hs : ∀ c : Conn, (c.start cfg ix now).drop = false := by
      intro d; unfold Conn.start; split <;> rfl
    split <;> simp_all [hs, Conn.expired, Bool.or_eq_true, Bool.and_eq_true]

theorem patience_drop_iff (ix : Index) (c : Conn) (now : Nat) (h : Held F)
    (hl : c.expired cfg now = false) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.drop = true ↔
      c.waiting = true ∧ c.waitStart + cfg.patience < now := by
  rw [tick_drop_iff]
  simp only [Conn.expired, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not] at hl
  rcases hl with hl | hl <;> simp_all <;> omega

theorem round_not_dropped (ix : Index) (c : Conn) (now t : Nat) (h : Held F)
    (hd : c.dialer = true) (hp : c.peerFloor.isSome = true)
    (ht : t ≤ now + cfg.patience) :
    (((c.start cfg ix now).conn.tick fam cfg ix t : HeldM F Step) h).1.drop = false := by
  apply Bool.eq_false_iff.mpr
  intro hdropped
  have hdropped := (tick_drop_iff fam cfg ix _ t h).1 hdropped
  cases hf : c.peerFloor with
  | none => simp [hf] at hp
  | some f => simp [Conn.start, hf, hd, Conn.waitStart] at hdropped; omega

theorem responder_expires (ix : Index) (c : Conn) (now : Nat) (h : Held F)
    (hd : c.dialer = false) (ht : c.heard + cfg.lease < now) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.drop = true :=
  (tick_drop_iff fam cfg ix c now h).2 (Or.inr ⟨hd, ht⟩)

/-- A dialer's arrival within one cadence keeps the responder's lease live.
Every decoded round (including its empty end) refreshes heard in recv. -/
theorem live_not_expired (c : Conn) (now : Nat)
    (hc : now ≤ c.heard + cfg.every) (hl : cfg.every ≤ cfg.lease) :
    c.expired cfg now = false := by
  simp [Conn.expired, show ¬c.heard + cfg.lease < now by omega]

/-- A shown room needs no pre-existing snapshot to answer a nonempty round. -/
theorem uncarried_room_answered (ix : Index) (c : Conn) (r : Id) (k now : Nat) (cs : List Claim)
    (hr : has c.rooms r = true) (hc : cs.isEmpty = false)
    (hn : c.snaps.find? (fun p => Decidable.decide (p.1 = (r, k))) = none) :
    (c.onRbsr cfg ix r k cs now).send.head? = some (Msg.rbsr r k
      ((cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (ix.items r))).filterMap
        fun | .claim x => some x | _ => none)).op := by
  simp [Conn.onRbsr, hr, hc, Conn.snap, hn]; rfl

end Engine.Sync
