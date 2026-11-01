/-
Every reachable connection bounds its stream hints, pending and visited
closure ids, and its round state (the rounds in flight, when each room's
last round opened, each room's epoch) as well as known and asked. Bounds
are preserved by every public entry point, including room changes. None
of them mentions the index: a connection holds no copy of a room, so its
state does not grow with a room's size, however many peers a hub has
mid-round.
-/
import engine.sync.BoundsLaws
import engine.sync.ClosureLaws
import engine.wire.WorldLaws

namespace Engine.Sync
attribute [local instance] byteArray_lawfulBEq

/-- The round state: at most one round in flight, one opening time and
one epoch per room carried, shown or taken. -/
def Conn.RoundBounded (c : Conn) : Prop :=
  c.active.length ≤ c.carried.length ∧ c.rounded.length ≤ c.carried.length ∧
    c.epochs.length ≤ c.carried.length ∧ c.short.length ≤ c.carried.length

/-- The additional bounds beyond known and asked. -/
def Conn.ExtraBounded (cfg : Config) (c : Conn) : Prop :=
  c.offered.size ≤ cfg.maxKnown ∧ c.ClosureBounded cfg ∧ c.RoundBounded

variable {F : Type} (fam : Family F) (cfg : Config)

theorem extra_begin (c : Conn) (k : Nat) (hb : c.ExtraBounded cfg) :
    (c.beginRound k).ExtraBounded cfg :=
  ⟨hb.1, begin_closure_bounded cfg c k hb.2.1, hb.2.2⟩

/-- Noting rooms one by one keeps at most `limit` records. -/
theorem notes_bounded (limit k : Nat) (rs : List Id) (es : List (Id × Nat)) (he : es.length ≤ limit) :
    (rs.foldl (fun es r => noteEpoch limit es r k) es).length ≤ limit := by
  induction rs generalizing es with
  | nil => exact he
  | cons r rs ih => exact ih _ (List.length_take_le ..)

theorem extra_start (ix : Index) (c : Conn) (now : Nat) (hb : c.ExtraBounded cfg) :
    (c.start cfg ix now).conn.ExtraBounded cfg := by
  unfold Conn.start
  split
  · exact hb
  · dsimp only
    split
    · exact hb
    · exact ⟨hb.1, begin_closure_bounded cfg c _ hb.2.1, List.length_take_le ..,
        notes_bounded _ _ _ _ hb.2.2.2.1, notes_bounded _ _ _ _ hb.2.2.2.2.1,
        Nat.le_trans (List.length_filter_le ..) hb.2.2.2.2.2⟩

theorem extra_ask (c : Conn) (now : Nat) (hb : c.ExtraBounded cfg) : (c.ask cfg now).conn.ExtraBounded cfg := by
  unfold Conn.ask
  split
  · exact hb
  · dsimp only
    split
    · exact hb
    · exact ⟨hb.1, hb.2.1, hb.2.2.1, notes_bounded _ _ _ _ hb.2.2.2.1, hb.2.2.2.2.1,
        Nat.le_trans (List.length_filter_le ..) hb.2.2.2.2.2⟩

theorem extra_onAsk (c : Conn) (r : Id) (hb : c.ExtraBounded cfg) : (c.onAsk r).ExtraBounded cfg := by
  unfold Conn.onAsk
  split
  · exact ⟨hb.1, hb.2.1, hb.2.2.1, Nat.le_trans (List.length_filter_le ..) hb.2.2.2.1, hb.2.2.2.2⟩
  · exact hb

theorem noteRoom_short (c : Conn) (r : Id) (cut : Bool) (hb : c.short.length ≤ c.carried.length) :
    (if cut = true then noteRoom c.carried.length c.short r else c.short).length ≤ c.carried.length := by
  split
  · exact List.length_take_le ..
  · exact hb

theorem extra_round (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hb : c.ExtraBounded cfg) : (c.onRbsr cfg ix r k cs now).conn.ExtraBounded cfg := by
  unfold Conn.onRbsr
  split
  · exact hb
  · split
    · exact hb
    rename_i fresh
    have hb' := extra_begin cfg c k hb
    have ht : ((c.beginRound k).active.filter (fun p => !Decidable.decide (p.1 = r))).length ≤ c.carried.length :=
      Nat.le_trans (List.length_filter_le ..) hb.2.2.1
    have hr : (if c.dialer = true then c.rounded else noteEpoch c.carried.length c.rounded r now).length ≤
        c.carried.length := by
      split
      · exact hb.2.2.2.1
      · exact List.length_take_le ..
    dsimp only
    split
    · exact ⟨hb'.1, hb'.2.1, ht, hr, List.length_take_le .., hb.2.2.2.2.2⟩
    · split
      · exact ⟨hb'.1, hb'.2.1, ht, hr, List.length_take_le .., noteRoom_short _ r _ hb.2.2.2.2.2⟩
      · exact ⟨hb'.1, hb'.2.1, List.length_take_le .., hr, List.length_take_le ..,
          noteRoom_short _ r _ hb.2.2.2.2.2⟩

theorem extra_hold (c : Conn) (r : Id) (ids : List Id) (h : Held F) (hb : c.ExtraBounded cfg) :
    ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.ExtraBounded cfg := by
  rw [onHold_apply]
  split
  · exact hb
  · split
    · exact hb
    · exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, noteRoom_short _ r _ hb.2.2.2.2.2⟩

theorem extra_want (ix : Index) (c : Conn) (ids : List Id) (hb : c.ExtraBounded cfg) :
    (c.onWant cfg ix ids).conn.ExtraBounded cfg := by
  unfold Conn.onWant
  split <;> exact hb

theorem extra_serve (c : Conn) (budget : Nat) (first : List Id) (h : Held F)
    (hb : c.ExtraBounded cfg) : ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.ExtraBounded cfg := by
  rw [serveOwed_eq]
  exact ⟨hb.1, queue_bounded cfg _ _ hb.2.1, hb.2.2⟩

theorem walk_offered (h : Held F) : ∀ fuel (c : Conn) offers,
    ((c.walkN fam cfg offers fuel : HeldM F _) h).1.1.offered = c.offered := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro c offers
    rw [Conn.walkN]
    cases c.frontier with
    | nil => rfl
    | cons x rest =>
      dsimp only
      split
      · exact ih _ _
      · rw [HeldM.bind_apply, HeldM.getOp_apply]
        cases h.db.ops x with
        | none => exact ih _ _
        | some o => dsimp only; split <;> exact ih _ _

/-- The closure walk leaves the round state alone. -/
theorem walk_rounds (h : Held F) : ∀ fuel (c : Conn) offers,
    let d := ((c.walkN fam cfg offers fuel : HeldM F _) h).1.1
    d.active = c.active ∧ d.rounded = c.rounded ∧ d.epochs = c.epochs ∧ d.short = c.short ∧
      d.takes = c.takes := by
  intro fuel
  induction fuel with
  | zero => intros; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ fuel ih =>
    intro c offers
    rw [Conn.walkN]
    cases c.frontier with
    | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | cons x rest =>
      dsimp only
      split
      · exact ih _ _
      · rw [HeldM.bind_apply, HeldM.getOp_apply]
        cases h.db.ops x with
        | none => exact ih _ _
        | some o => dsimp only; split <;> exact ih _ _

theorem extra_walk (h : Held F) (c : Conn) (hb : c.ExtraBounded cfg) :
    ((c.walk fam cfg : HeldM F _) h).1.1.ExtraBounded cfg := by
  have hk := walk_keeps fam cfg h c
  obtain ⟨e1, e2, e3, e4, e5⟩ := walk_rounds fam cfg h cfg.walk c []
  exact ⟨by simpa [Conn.walk, walk_offered] using hb.1,
    closure_capped fam cfg h cfg.walk c [] hb.2.1,
    by simp only [Conn.RoundBounded, Conn.carried, Conn.walk, e1, e2, e3, e4, e5]; rw [← Conn.walk, hk.2.1]; exact hb.2.2⟩

theorem extra_tick (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hb : c.ExtraBounded cfg) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.conn.ExtraBounded cfg := by
  unfold Conn.tick Conn.work
  split
  · exact hb
  · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_conn]
    have hw := extra_walk fam cfg h c hb
    have he : ((c.walk fam cfg : HeldM F _) h).1.1.expireAsks cfg now |>.ExtraBounded cfg := hw
    split
    · exact extra_start cfg _ _ _ he
    · exact extra_ask cfg _ _ he

theorem extra_recv (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (h : Held F)
    (hb : c.ExtraBounded cfg) : ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.conn.ExtraBounded cfg := by
  unfold Conn.recv
  cases Op.decode bytes with
  | none => exact hb
  | some o =>
    dsimp only
    cases Msg.ofOp o with
    | none =>
      dsimp only
      split
      · exact hb
      · exact hb
    | some msg =>
      cases msg with
      | hello f =>
        dsimp only
        split
        · exact extra_start cfg _ _ _ hb
        · exact ⟨hb.1, hb.2.1, hb.2.2.1, by simp [Conn.carried], hb.2.2.2.2⟩
      | rbsr r k cs => exact (extra_round cfg _ _ _ _ _ _ hb)
      | hold r ids =>
        dsimp only
        split
        · exact extra_onAsk cfg _ r hb
        · exact (extra_hold fam cfg _ _ _ _ hb)
      | want ids =>
        dsimp only
        exact (extra_want cfg _ _ _ hb)

theorem extra_filed (c : Conn) (ids : List Id) (h : Held F) (hb : c.ExtraBounded cfg) :
    ((c.filed fam cfg ids : HeldM F Step) h).1.conn.ExtraBounded cfg := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam cfg h.db)]
  · exact foldl_inv (fun b : List (Id × Id) × Conn => b.2.ExtraBounded cfg) (fileOffer fam cfg h.db)
      (by intro b i hb; unfold fileOffer; split <;> try exact hb
          split <;> try exact hb
          split
          · exact ⟨remember_bounded .., hb.2⟩
          · exact hb) ids ([], c) hb
  · intro a b
    unfold fileOffer
    split
    · rw [HeldM.bind_apply, HeldM.getOp_apply]
      cases h.db.ops a with
      | none => rfl
      | some o => dsimp only; split <;> rfl
    · rfl

/-- Giving a notice changes only the once-only record, not sync's caps. -/
theorem extra_give (h : Held F) : ∀ (ns : List (Id × Id)) (c : Conn),
    c.ExtraBounded cfg → ((c.give fam cfg ns : HeldM F Step) h).1.conn.ExtraBounded cfg
  | [], c, hb => hb
  | (r, x) :: rest, c, hb => by
    unfold Conn.give
    split
    · exact extra_give h rest c hb
    · simp only [HeldM.bind_apply, HeldM.pure_apply]
      exact extra_give _ rest _ hb

/-- **A connection's state does not grow with a room's size.** Every
reachable state has all five id collections bounded by constants, and
its round state by its number of rooms: at most one round in flight, one
opening time, one epoch and one short mark per room carried (shown or
taken). No bound
mentions the index
(every transition is taken over any index): no connection holds a copy
of a room, however large the room or however many peers are mid-round. -/
theorem conn_state_bounded {c : Conn} (hc : c.Reachable fam cfg) :
    c.known.size ≤ cfg.maxKnown ∧ c.asked.size ≤ cfg.maxKnown ∧
    c.offered.size ≤ cfg.maxKnown ∧ c.closed.size + c.frontier.length ≤ cfg.closureCap ∧
    c.active.length ≤ c.carried.length ∧ c.rounded.length ≤ c.carried.length ∧
    c.epochs.length ≤ c.carried.length ∧ c.short.length ≤ c.carried.length := by
  have hb := conn_bounded fam cfg hc
  refine ⟨hb.1, hb.2, ?_⟩
  change c.ExtraBounded cfg
  clear hb
  induction hc with
  | «open» => simp [Conn.open, Conn.ExtraBounded, Conn.ClosureBounded, Conn.RoundBounded]
  | start _ _ _ ih => exact extra_start cfg _ _ _ ih
  | round _ _ _ _ _ _ ih => exact extra_round cfg _ _ _ _ _ _ ih
  | hold _ _ _ _ ih => exact extra_hold fam cfg _ _ _ _ ih
  | want _ _ _ ih => exact extra_want cfg _ _ _ ih
  | serve _ _ _ _ ih => exact extra_serve fam cfg _ _ _ _ ih
  | recv _ _ _ _ _ ih => exact extra_recv fam cfg _ _ _ _ _ ih
  | tick _ _ _ _ ih => exact extra_tick fam cfg _ _ _ _ ih
  | filed _ _ _ ih => exact extra_filed fam cfg _ _ _ ih
  | rooms _ _ ih => exact ⟨ih.1, ih.2.1, List.length_take_le .., List.length_take_le .., List.length_take_le ..,
      List.length_take_le ..⟩
  | carry _ _ ih => exact ⟨ih.1, ih.2.1, List.length_take_le .., List.length_take_le .., List.length_take_le ..,
      List.length_take_le ..⟩
  | notify _ _ ih => exact extra_give fam cfg _ _ _ ih

end Engine.Sync
