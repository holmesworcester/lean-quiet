/-
One silence deadline for both sides. Empty haves are keepalives; asks
expire separately. Time is logical milliseconds, with no pause accounting.
-/
import ops.sync.ServeLaws
import Std.Data.HashSet.Lemmas

namespace Engine.Sync
local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data
variable {F : Type} (fam : Family F) (cfg : Config)

theorem work_no_drop (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((c.work fam cfg ix now : HeldM F Step) h).1.drop = false := by
  unfold Conn.work
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  split
  · unfold Conn.start; split <;> rfl
  · rfl

/-- Both roles drop exactly at the strict silence deadline. -/
theorem drop_iff_silent (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.drop = true ↔ c.heard + cfg.live < now := by
  unfold Conn.tick
  split
  · simp_all [HeldM.pure_apply]
  · simp_all only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_drop, work_no_drop,
      Bool.false_eq_true]

/-- A quiet live tick sends the existing empty-have message when due. -/
theorem keepalive_sent (ix : Index) (c : Conn) (now : Nat) (h : Held F)
    (hl : now ≤ c.heard + cfg.live) (hd : c.sent + cfg.live / 3 ≤ now)
    (hq : ((c.work fam cfg ix now : HeldM F Step) h).1.send = []) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.send = [(Msg.hold .empty []).op] := by
  simp [Conn.tick, show ¬ c.heard + cfg.live < now by omega,
    HeldM.bind_apply, HeldM.pure_apply, Step.pulse, hq, hd]

/-- Each live tick either sends something or has sent within one interval. -/
theorem tick_sends_or_recent (ix : Index) (c : Conn) (now : Nat) (h : Held F)
    (hl : now ≤ c.heard + cfg.live) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.send ≠ [] ∨ now < c.sent + cfg.live / 3 := by
  unfold Conn.tick
  rw [if_neg (show ¬ c.heard + cfg.live < now by omega)]
  simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse]
  split
  · exact Or.inl (by simp)
  · rename_i hn
    by_cases he : ((c.work fam cfg ix now : HeldM F Step) h).1.send = []
    · right; simp [he] at hn; omega
    · exact Or.inl he

/-- The scheduler's last tick before the delivery margin. A scheduler
that ticks at least every live/3 supplies one in this two-interval window.
The two delivery premises cover its new output or its preceding output;
both are old enough to have arrived with latency at most live/3. -/
theorem peer_keeps_live (ix iy : Index) (peer c : Conn) (atTick now : Nat) (h g : Held F)
    (hp : atTick ≤ peer.heard + cfg.live)
    (hs : now ≤ atTick + 2 * (cfg.live / 3))
    (hq : ((peer.tick fam cfg ix atTick : HeldM F Step) h).1.send = [] → peer.sent ≤ c.heard)
    (hd : ((peer.tick fam cfg ix atTick : HeldM F Step) h).1.send ≠ [] → atTick ≤ c.heard) :
    ((c.tick fam cfg iy now : HeldM F Step) g).1.drop = false := by
  apply Bool.eq_false_iff.mpr
  intro dropped
  have silence := (drop_iff_silent fam cfg iy c now g).mp dropped
  have thirds : 3 * (cfg.live / 3) ≤ cfg.live := by omega
  rcases tick_sends_or_recent fam cfg ix peer atTick h hp with sent | recent
  · have := hd sent; omega
  · by_cases sent : ((peer.tick fam cfg ix atTick : HeldM F Step) h).1.send = []
    · have := hq sent; omega
    · have := hd sent; omega

/-- Two actual tick histories never drop each other. The scheduler supplies
one tick in the interval ending one delivery margin ago. Delivery covers
that tick's output, or the preceding output remembered in sent. These are
scheduler/transport assumptions, not an assumed bound on silence. -/
theorem live_stays (ia ib : Nat → Index) (a b : Nat → Conn) (ha hb : Nat → Held F)
    (ta tb : Nat → Prop) (positive : 0 < cfg.live / 3)
    (scheduleA : ∀ now, cfg.live < now → ∃ t, ta t ∧ t + cfg.live / 3 ≤ now ∧ now ≤ t + 2 * (cfg.live / 3))
    (scheduleB : ∀ now, cfg.live < now → ∃ t, tb t ∧ t + cfg.live / 3 ≤ now ∧ now ≤ t + 2 * (cfg.live / 3))
    (deliverA : ∀ now t, ta t → t + cfg.live / 3 ≤ now →
      ((((a t).tick fam cfg (ia t) t : HeldM F Step) (ha t)).1.send = [] → (a t).sent ≤ (b now).heard) ∧
      ((((a t).tick fam cfg (ia t) t : HeldM F Step) (ha t)).1.send ≠ [] → t ≤ (b now).heard))
    (deliverB : ∀ now t, tb t → t + cfg.live / 3 ≤ now →
      ((((b t).tick fam cfg (ib t) t : HeldM F Step) (hb t)).1.send = [] → (b t).sent ≤ (a now).heard) ∧
      ((((b t).tick fam cfg (ib t) t : HeldM F Step) (hb t)).1.send ≠ [] → t ≤ (a now).heard)) :
    ∀ now, ((((a now).tick fam cfg (ia now) now : HeldM F Step) (ha now)).1.drop = false) ∧
      ((((b now).tick fam cfg (ib now) now : HeldM F Step) (hb now)).1.drop = false) := by
  intro now
  induction now using Nat.strongRecOn with
  | ind now ih =>
    by_cases initial : now ≤ cfg.live
    · constructor <;> apply Bool.eq_false_iff.mpr <;> intro dropped
      · have := (drop_iff_silent fam cfg (ia now) (a now) now (ha now)).mp dropped; omega
      · have := (drop_iff_silent fam cfg (ib now) (b now) now (hb now)).mp dropped; omega
    · obtain ⟨t, ht, old, near⟩ := scheduleA now (by omega)
      obtain ⟨u, hu, old', near'⟩ := scheduleB now (by omega)
      have prevA := (ih t (by omega)).1
      have prevB := (ih u (by omega)).2
      have aliveA : t ≤ (a t).heard + cfg.live := by
        by_cases good : t ≤ (a t).heard + cfg.live
        · exact good
        · have := (drop_iff_silent fam cfg (ia t) (a t) t (ha t)).mpr (by omega)
          simp [prevA] at this
      have aliveB : u ≤ (b u).heard + cfg.live := by
        by_cases good : u ≤ (b u).heard + cfg.live
        · exact good
        · have := (drop_iff_silent fam cfg (ib u) (b u) u (hb u)).mpr (by omega)
          simp [prevB] at this
      exact ⟨peer_keeps_live fam cfg (ib u) (ia now) (b u) (a now) u now (hb u) (ha now)
          aliveB near' (deliverB now u hu old').1 (deliverB now u hu old').2,
        peer_keeps_live fam cfg (ia t) (ib now) (a t) (b now) t now (ha t) (hb now)
          aliveA near (deliverA now t ht old).1 (deliverA now t ht old).2⟩

/-- The quiet-tick premise is inhabited for either role with no rooms. -/
theorem keepalive_runs (dialer : Bool) :
    let c := (Conn.open dialer [] 0 0).conn
    ((c.tick fam cfg {} (cfg.live / 3) : HeldM F Step) {}).1.send = [(Msg.hold .empty []).op] := by
  apply keepalive_sent fam cfg
  · simp [Conn.open]; omega
  · simp [Conn.open]
  · have empty_filter (p : Id → Bool) : (({} : Std.HashSet Id).filter p).toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hs := Std.HashSet.size_filter_le_size (m := ({} : Std.HashSet Id)) (f := p)
      simpa using hs
    cases hw : cfg.walk <;> simp [Conn.work, Conn.open, Conn.walk, Conn.walkN, hw, Conn.expireAsks,
      Conn.retryIds, Conn.start, holdsOf, chunks, pieceIds, Std.HashSet.toList_empty, empty_filter] <;>
      split <;> simp [pieceIds]

/-- An unshown room gets an empty end and leaves connection state alone. -/
theorem unshown_room_answered (ix : Index) (c : Conn) (r : Id) (k now : Nat) (cs : List Claim)
    (hr : has c.rooms r = false) :
    c.onRbsr cfg ix r k cs now = { conn := c, send := [(Msg.rbsr r k []).op] } := by
  simp [Conn.onRbsr, hr]

/-- Any shown idle room starts, regardless of other rooms' snapshots. -/
theorem room_independent (ix : Index) (c : Conn) (r : Id) (now pf : Nat)
    (hp : c.peerFloor = some pf) (hr : r ∈ c.rooms)
    (idle : c.snaps.any (fun p => p.1.1 == r) = false) :
    (Msg.rbsr r (c.round + 1)
      ((window (max c.floor pf)).map (opening Prod.fst Prod.snd sha256 cfg.params (ix.items r)))).op ∈
      (c.start cfg ix now).send := by
  simp only [Conn.start, hp, List.mem_map]
  refine ⟨((r, c.round + 1), ix.items r), ?_, rfl⟩
  exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [idle]⟩, rfl⟩

/-- A shown room answers independently of whether another room has a snapshot. -/
theorem uncarried_room_answered (ix : Index) (c : Conn) (r : Id) (k now : Nat) (cs : List Claim)
    (hr : has c.rooms r = true) (hc : cs.isEmpty = false)
    (hn : c.snaps.find? (fun p => Decidable.decide (p.1 = (r, k))) = none) :
    (c.onRbsr cfg ix r k cs now).send.head? = some (Msg.rbsr r k
      ((cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (ix.items r))).filterMap
        fun | .claim x => some x | _ => none)).op := by
  simp [Conn.onRbsr, hr, hc, Conn.snap, hn]; rfl

end Engine.Sync
