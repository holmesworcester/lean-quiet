/-
Bounds do not end sessions: honest_no_drop classifies every dropping
connection call as a timer expiry. Asks age by periods of patience,
whatever the traffic, so an ask the peer never answers (its op purged)
expires within two periods (`asks_expire`); nothing is retried, since a
want is served whole (ServeLaws, `owed_within`).
-/
import ops.sync.TimeLaws
import ops.sync.BoundsLaws
import engine.wire.WorldLaws

namespace Engine.Sync
attribute [local instance] byteArray_lawfulBEq
variable {F : Type} (fam : Family F) (cfg : Config)

theorem known_forgets (cap : Nat) (known : Std.HashSet Id) (i : Id)
    (hp : 0 < cap) (hf : cap < (known.insert i).size) :
    remember cap known i = ({} : Std.HashSet Id).insert i := by
  simp [remember, show cap ≠ 0 by omega, show ¬ (known.insert i).size ≤ cap by omega]

/-- **Asks are never deferred:** every id offered that is not already
asked is wanted, whatever the asks hold (the cap only limits what is
remembered, `noteAsks`). -/
theorem asks_all (asked stale : Std.HashSet Id) (ids : List Id) (i : Id) (hi : i ∈ ids)
    (ha : asked.contains i = false) (hs : stale.contains i = false) : i ∈ freshAsks asked stale ids :=
  List.mem_eraseDups.2 (List.mem_filter.2 ⟨hi, by simp [ha, hs]⟩)

theorem round_no_drop (ix : Index) (c : Conn) (r : Id) (k now : Nat) (cs : List Claim) :
    (c.onRbsr cfg ix r k cs now).drop = false := by
  unfold Conn.onRbsr
  split
  · rfl
  · dsimp only; split
    · rfl
    · exact Step.limit_drop _ _

theorem hold_no_drop (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    ((c.onHold fam cfg r ids : HeldM F Step) h).1.drop = false := by
  rw [onHold_apply]; split
  · rfl
  · split
    · rfl
    · exact Step.limit_drop _ _

theorem want_no_drop (ix : Index) (c : Conn) (ids : List Id) :
    (c.onWant cfg ix ids).drop = false := onWant_drop cfg ix c ids

theorem recv_no_drop (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (h : Held F) :
    ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.drop = false := by
  unfold Conn.recv
  cases hd : Op.decode bytes with
  | none => rfl
  | some o =>
    dsimp only
    cases hm : Msg.ofOp o with
    | none =>
      dsimp only
      split <;> simp [HeldM.pure_apply, Conn.finish, Step.limit_drop]
    | some msg =>
      cases msg with
      | hello f =>
        change (Conn.finish _).drop = false
        rw [Conn.finish_drop]
        split <;> rfl
      | rbsr r k cs => exact round_no_drop cfg _ _ _ _ _ _
      | hold r ids => simp only [HeldM.bind_apply, HeldM.pure_apply, Conn.finish_drop]; exact hold_no_drop fam cfg _ _ _ _
      | want ids => simp only [HeldM.pure_apply, Conn.finish_drop]; exact want_no_drop cfg _ _ _

/-- An observed return from a public Conn entry point, using the running code. -/
inductive Conn.Call (fam : Family F) (cfg : Config) (c : Conn) (now : Nat) (h : Held F) : Step → Prop where
  | open (dialer rooms floor) : Call fam cfg c now h (Conn.open dialer rooms floor now)
  | start (ix) : Call fam cfg c now h (c.start cfg ix now)
  | round (ix r k cs) : Call fam cfg c now h (c.onRbsr cfg ix r k cs now)
  | hold (r ids) : Call fam cfg c now h ((c.onHold fam cfg r ids : HeldM F Step) h).1
  | want (ix ids) : Call fam cfg c now h (c.onWant cfg ix ids)
  | recv (ix bytes) : Call fam cfg c now h ((c.recv fam cfg ix bytes now : HeldM F Step) h).1
  | tick (ix) : Call fam cfg c now h ((c.tick fam cfg ix now : HeldM F Step) h).1
  | filed (ids) : Call fam cfg c now h ((c.filed fam cfg ids : HeldM F Step) h).1

/-- No set size or message handler drops a connection. Transport errors
and retirement enter Node's close path; within Conn only timers drop. -/
theorem honest_no_drop (c : Conn) (now : Nat) (h : Held F) (s : Step)
    (call : c.Call fam cfg now h s) (hd : s.drop = true) :
    (c.waiting = true ∧ c.waitStart + cfg.patience < now) ∨
      (c.dialer = false ∧ c.heard + cfg.lease < now) := by
  cases call with
  | «open» => cases hd
  | start ix => unfold Conn.start at hd; split at hd <;> cases hd
  | round ix r k cs => rw [round_no_drop] at hd; cases hd
  | hold r ids => rw [hold_no_drop] at hd; cases hd
  | want ix ids => rw [want_no_drop] at hd; cases hd
  | recv ix bytes => rw [recv_no_drop] at hd; cases hd
  | tick ix => exact (tick_drop_iff fam cfg ix c now h).1 hd
  | filed ids => simp [Conn.filed, HeldM.bind_apply, HeldM.pure_apply, Conn.finish] at hd

/-- The dropping premise is inhabited: a silent responder really expires. -/
theorem honest_no_drop_runs :
    ∃ (c : Conn) (s : Step), c.Call fam cfg (cfg.lease + 1) ({} : Held F) s ∧ s.drop = true := by
  let c : Conn := { dialer := false, rooms := [], floor := 0, peerFloor := some 0 }
  refine ⟨c, _, .tick {}, ?_⟩
  exact responder_expires fam cfg {} c (cfg.lease + 1) {} rfl (by simp [c])

/-- **An unanswered ask expires.** Two period ends after an ask (each
at least `patience` after the last), it is in neither set, so the next
offer of the op asks for it again. The peer may have purged the op, or
not queued the want: no ask waits forever. -/
theorem asks_expire (c : Conn) (now₁ now₂ : Nat) (h1 : c.askedAt + cfg.patience ≤ now₁)
    (h2 : now₁ + cfg.patience ≤ now₂) :
    ((c.age cfg now₁).age cfg now₂).asked = {} ∧ ((c.age cfg now₁).age cfg now₂).stale = {} := by
  simp [Conn.age, h1, h2]

/-- And an ask lasts at least one period: aging keeps this period's
asks as the last period's. -/
theorem asks_last (c : Conn) (now : Nat) (i : Id) (hi : i ∈ c.asked) :
    i ∈ (c.age cfg now).asked ∨ i ∈ (c.age cfg now).stale := by
  unfold Conn.age; split
  · exact Or.inr hi
  · exact Or.inl hi

end Engine.Sync
