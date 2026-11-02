/-
Rounds open on events, proven of the running `Conn.tick` and `Conn.recv`
for both ends of a session (docs/SYNC.md, "Rounds"):

- `round_due`: the dialer's tick opens a round in every shown room that
  is due (`Conn.due`: none yet on this session, or the last opened
  `safety` ms ago or more) or short (`Conn.retake`), with the opening
  claims of the live index.
- `shown_due`: a room a session starts showing is due, so the dialer's
  next tick opens it (and the responder's asks for one).
- `responder_asks`: the responder's tick asks for a round in each shown
  room it has seen no round in, with an empty have naming it; `ask_due`:
  the dialer that hears it makes the room due.
- `no_round_before_safety`: with no event, a tick opens no round in a
  room whose last round opened less than `safety` ms ago;
  `responder_opens_none`: the responder's tick opens none at all.
- `join_round`: whichever end starts showing a room, a round in it opens
  at the dialer's next tick (the dialer showed it last), or at the
  dialer's tick after it hears the responder's ask: two ticks and one
  delivery.
-/
import engine.sync.StateLaws
import engine.sync.TimeLaws

namespace Engine.Sync
attribute [local instance] byteArray_lawfulBEq

section
variable {F : Type} (fam : Family F) (cfg : Config)

/-- A pulse only fills an empty send. -/
theorem pulse_mem (s : Step) (sent now : Nat) (x : Op) (hx : x ∈ s.send) : x ∈ (s.pulse cfg sent now).send := by
  unfold Step.pulse
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    rw [h.1] at hx; cases hx
  · exact hx

/-- Room r is due at `now` exactly when no round of it opened on this
session, or the last opened `safety` ms ago or more. -/
theorem due_iff (c : Conn) (r : Id) (now : Nat) :
    c.due cfg r now = true ↔ c.roundedAt r = none ∨ ∃ t, c.roundedAt r = some t ∧ t + cfg.safety ≤ now := by
  unfold Conn.due
  cases c.roundedAt r <;> simp

/-- Fewer asks keep a short room due again. -/
theorem retake_fewer {c d : Conn} (r : Id) (hs : d.short = c.short) (ha : d.active = c.active)
    (hk : d.asked.size ≤ c.asked.size) (h : c.retake cfg r = true) : d.retake cfg r = true := by
  unfold Conn.retake at *
  rw [hs, ha]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, by omega⟩, by omega⟩

/-- What the tick's work starts from: the connection after expiry, which
keeps everything the round decisions read but the asks. -/
theorem work_base (c : Conn) (now : Nat) :
    ∃ d : Conn, c.expireAsks cfg now = d ∧
      d.dialer = c.dialer ∧ d.peerFloor = c.peerFloor ∧ d.floor = c.floor ∧ d.rooms = c.rooms ∧
      d.round = c.round ∧ d.rounded = c.rounded ∧ d.active = c.active ∧ d.short = c.short ∧
      d.asked.size ≤ c.asked.size :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Std.HashSet.size_filter_le_size⟩

theorem tick_work (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hl : now ≤ c.heard + cfg.live) (x : Op)
    (hx : x ∈ ((c.work fam cfg ix now : HeldM F Step) h).1.send) :
    x ∈ ((c.tick fam cfg ix now : HeldM F Step) h).1.send := by
  unfold Conn.tick
  rw [if_neg (by omega)]
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  exact pulse_mem cfg _ _ _ x hx

/-- **The dialer opens every due room's round.** On a live session whose
peer's floor it knows, the dialer's tick sends, for each shown room that
is due or short, the round's opening: the claims of the live index over
the two windows' overlap. -/
theorem round_due (ix : Index) (c : Conn) (r : Id) (now pf : Nat) (h : Held F)
    (hd : c.dialer = true) (hp : c.peerFloor = some pf) (hr : r ∈ c.rooms)
    (hl : now ≤ c.heard + cfg.live) (due : (c.due cfg r now || c.retake cfg r) = true) :
    (Msg.rbsr r (c.round + 1)
      ((window 0).map (opening Prod.fst Prod.snd sha256 cfg.params
        (ix.over cfg.params.depth r (max c.floor pf))))).op ∈
      ((c.tick fam cfg ix now : HeldM F Step) h).1.send := by
  apply tick_work fam cfg ix c now h hl
  obtain ⟨d, ed, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := work_base cfg c now
  unfold Conn.work
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  rw [ed, if_pos (by rw [e1]; exact hd)]
  apply List.mem_append_left
  have due' : (d.due cfg r now || d.retake cfg r) = true := by
    have hdue : d.due cfg r now = c.due cfg r now := by unfold Conn.due Conn.roundedAt; rw [e6]
    rw [hdue]
    cases hc : c.due cfg r now
    · rw [hc, Bool.false_or] at due; rw [Bool.false_or]; exact retake_fewer cfg r e8 e7 e9 due
    · rfl
  have := room_independent cfg ix d r now pf (by rw [e2, hp]) (by rw [e4]; exact hr) due'
  rwa [e5, e3] at this

/-- `noteEpoch` records its room's value, first. -/
theorem roundedAt_note (limit : Nat) (rs : List (Id × Nat)) (r : Id) (t : Nat) (hl : 0 < limit) :
    ((noteEpoch limit rs r t).find? fun p => Decidable.decide (p.1 = r)) = some (r, t) := by
  obtain ⟨n, rfl⟩ : ∃ n, limit = n + 1 := ⟨limit - 1, by omega⟩
  simp [noteEpoch]

/-- **A room a session starts showing is due.** Showing it anew (it was
not among the rooms) leaves no record of a round in it: the dialer's
next tick opens one (`round_due`), the responder's asks for one
(`responder_asks`). -/
theorem shown_due (c : Conn) (rs : List Id) (r : Id) (now : Nat) (hnew : r ∉ c.rooms) :
    (c.setRooms rs).roundedAt r = none ∧ (c.setRooms rs).due cfg r now = true := by
  have hn : (c.setRooms rs).roundedAt r = none := by
    unfold Conn.roundedAt Conn.setRooms
    simp only [Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
    intro p hp e
    have := (List.mem_filter.1 (List.mem_of_mem_take hp)).2
    simp only [Bool.and_eq_true] at this
    exact hnew (e ▸ (Engine.has_iff _ _).1 this.2)
  exact ⟨hn, by unfold Conn.due; rw [hn]⟩

/-- **The responder asks for a round in a room it starts showing.** On a
live session whose peer's floor it knows, the responder's tick sends an
empty have naming each shown room it has neither seen a round in nor
asked about. -/
theorem responder_asks (ix : Index) (c : Conn) (r : Id) (now pf : Nat) (h : Held F)
    (hd : c.dialer = false) (hp : c.peerFloor = some pf) (hr : r ∈ c.rooms)
    (hl : now ≤ c.heard + cfg.live) (fresh : c.roundedAt r = none) :
    (Msg.hold r []).op ∈ ((c.tick fam cfg ix now : HeldM F Step) h).1.send := by
  apply tick_work fam cfg ix c now h hl
  obtain ⟨d, ed, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := work_base cfg c now
  unfold Conn.work
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  rw [ed, if_neg (by rw [e1, hd]; simp)]
  apply List.mem_append_left
  have hm : r ∈ d.rooms.filter fun r => (d.roundedAt r).isNone || d.retake cfg r := by
    refine List.mem_filter.2 ⟨by rw [e4]; exact hr, ?_⟩
    have : d.roundedAt r = c.roundedAt r := by unfold Conn.roundedAt; rw [e6]
    rw [this, fresh]; rfl
  have hne : (d.rooms.filter fun r => (d.roundedAt r).isNone || d.retake cfg r).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hm)
  unfold Conn.ask
  rw [e2, hp]
  simp only [hne, Bool.false_eq_true, ite_false, List.mem_map]
  exact ⟨r, hm, rfl⟩

/-- **The dialer that hears an ask makes the room due.** An empty have
naming a shown room with no round of it in flight leaves no record of a
round in it, so the dialer's next tick opens one. -/
theorem ask_due (ix : Index) (c : Conn) (r : Id) (now later : Nat) (h : Held F)
    (hd : c.dialer = true) (hr : r ∈ c.rooms) (idle : c.active.any (fun p => Decidable.decide (p.1 = r)) = false) :
    let d := ((c.recv fam cfg ix (Msg.hold r []).op.bytes now : HeldM F Step) h).1
    d.send = [] ∧ d.conn.roundedAt r = none ∧ d.conn.due cfg r later = true := by
  intro d
  have hd' : d = { conn := ({ c with heard := now } : Conn).onAsk r } := by
    simp [d, Conn.recv, Op.decode_bytes, ofOp_hold]
  have hn : d.conn.roundedAt r = none := by
    rw [hd']
    unfold Conn.onAsk
    rw [if_pos (by simp [hd, has_of_mem hr, idle])]
    unfold Conn.roundedAt
    simp
  refine ⟨by rw [hd'], hn, ?_⟩
  unfold Conn.due; rw [hn]

/-- An opening names its room. -/
theorem rbsr_room {r r' : Id} {k k' : Nat} {cs cs' : List Claim}
    (e : (Msg.rbsr r k cs).op = (Msg.rbsr r' k' cs').op) : r = r' := by
  have := congrArg Op.reqs e
  simpa [Msg.op] using this

theorem rbsr_not_hold (r r' : Id) (k : Nat) (cs : List Claim) (ids : List Id) :
    (Msg.rbsr r k cs).op ≠ (Msg.hold r' ids).op := by
  intro e; have := congrArg Op.kind e; simp [Msg.op, kRbsr, kHave] at this

theorem rbsr_not_want (r : Id) (k : Nat) (cs : List Claim) (ids : List Id) :
    (Msg.rbsr r k cs).op ≠ (Msg.want ids).op := by
  intro e; have := congrArg Op.kind e; simp [Msg.op, kRbsr, kWant] at this

theorem rbsr_not_chunk (r : Id) (k : Nat) (cs : List Claim) (ids : List Id) (mk : List Id → Msg)
    (hmk : ∀ l, (∃ r', mk l = .hold r' l) ∨ mk l = .want l) :
    (Msg.rbsr r k cs).op ∉ chunks cfg ids mk := by
  intro hm
  simp only [chunks, List.mem_map] at hm
  obtain ⟨l, _, e⟩ := hm
  rcases hmk l with ⟨r', h⟩ | h <;> rw [h] at e
  · exact rbsr_not_hold r r' k cs l e.symm
  · exact rbsr_not_want r k cs l e.symm

/-- What a tick's work sends besides the dialer's openings: offers, the
responder's asks, retried wants. None opens a round. -/
theorem work_no_rbsr (ix : Index) (c : Conn) (now : Nat) (h : Held F) (r : Id) (k : Nat) (cs : List Claim)
    (hs : ∀ d : Conn, d.dialer = c.dialer → d.rooms = c.rooms → d.rounded = c.rounded →
      d.short = c.short → d.active = c.active → d.asked.size ≤ c.asked.size →
      (Msg.rbsr r k cs).op ∉ (if d.dialer then d.start cfg ix now else d.ask cfg now).send) :
    (Msg.rbsr r k cs).op ∉ ((c.work fam cfg ix now : HeldM F Step) h).1.send := by
  obtain ⟨d, ed, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := work_base cfg c now
  unfold Conn.work
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  rw [ed]
  intro hm
  rcases List.mem_append.1 hm with hm | hm
  · exact hs d e1 e4 e6 e8 e7 e9 hm
  · exact rbsr_not_chunk cfg r k cs _ _ (fun l => Or.inr rfl) hm

theorem tick_no_rbsr (ix : Index) (c : Conn) (now : Nat) (h : Held F) (r : Id) (k : Nat) (cs : List Claim)
    (hw : (Msg.rbsr r k cs).op ∉ ((c.work fam cfg ix now : HeldM F Step) h).1.send) :
    (Msg.rbsr r k cs).op ∉ ((c.tick fam cfg ix now : HeldM F Step) h).1.send := by
  unfold Conn.tick
  split
  · simp
  · simp only [HeldM.bind_apply, HeldM.pure_apply]
    unfold Step.pulse
    split
    · simp only [List.mem_singleton]; exact rbsr_not_hold r .empty k cs []
    · exact hw

theorem ask_no_rbsr (c : Conn) (now : Nat) (r : Id) (k : Nat) (cs : List Claim) :
    (Msg.rbsr r k cs).op ∉ (c.ask cfg now).send := by
  unfold Conn.ask
  split
  · simp
  · dsimp only; split
    · simp
    · simp only [List.mem_map, not_exists, not_and]
      intro r' _ e
      exact rbsr_not_hold r r' k cs [] e.symm

/-- **The responder opens no round.** -/
theorem responder_opens_none (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hd : c.dialer = false)
    (r : Id) (k : Nat) (cs : List Claim) :
    (Msg.rbsr r k cs).op ∉ ((c.tick fam cfg ix now : HeldM F Step) h).1.send := by
  apply tick_no_rbsr fam cfg ix c now h r k cs
  apply work_no_rbsr fam cfg ix c now h r k cs
  intro d e1 _ _ _ _ _
  rw [if_neg (by rw [e1, hd]; simp)]
  exact ask_no_rbsr cfg d now r k cs

/-- **With no event, no round before the safety period.** A tick opens no
round in a room whose last round opened less than `safety` ms ago and
which is not short: no wakeup, no traffic for it. -/
theorem no_round_before_safety (ix : Index) (c : Conn) (now : Nat) (h : Held F) (r : Id) (t : Nat)
    (ht : c.roundedAt r = some t) (early : now < t + cfg.safety) (hs : has c.short r = false)
    (k : Nat) (cs : List Claim) :
    (Msg.rbsr r k cs).op ∉ ((c.tick fam cfg ix now : HeldM F Step) h).1.send := by
  apply tick_no_rbsr fam cfg ix c now h r k cs
  apply work_no_rbsr fam cfg ix c now h r k cs
  intro d _ _ e3 e4 _ _
  split
  · unfold Conn.start
    split
    · simp
    · dsimp only; split
      · simp
      · simp only [List.mem_map, not_exists, not_and]
        intro r' hr' e
        have er := rbsr_room e
        rw [er] at hr'
        have := (List.mem_filter.1 hr').2
        have hdue : d.due cfg r now = false := by
          have : d.roundedAt r = some t := by unfold Conn.roundedAt; rw [e3]; exact ht
          unfold Conn.due; rw [this]; simp; omega
        have hret : d.retake cfg r = false := by
          unfold Conn.retake; rw [e4, hs]; rfl
        rw [hdue, hret] at this; cases this
  · exact ask_no_rbsr cfg d now r k cs

/-- **Whichever end starts showing a room, a round in it opens.** If the
responder started showing room r last, its tick asks for a round
(`responder_asks`); the dialer, hearing the ask while no round of r is
in flight, opens one at its next live tick (`ask_due`, `round_due`). If
the dialer started showing r last, `shown_due` and `round_due` open it
at its next tick. So a round opens within two ticks and one delivery of
either end starting to show the room. -/
theorem join_round (ix iy : Index) (a b : Conn) (r : Id) (t1 t2 t3 pfa pfb : Nat) (ha hb : Held F)
    (hda : a.dialer = true) (hdb : b.dialer = false)
    (hpa : a.peerFloor = some pfa) (hpb : b.peerFloor = some pfb)
    (hra : r ∈ a.rooms) (hrb : r ∈ b.rooms) (fresh : b.roundedAt r = none)
    (idle : a.active.any (fun p => Decidable.decide (p.1 = r)) = false)
    (hlb : t1 ≤ b.heard + cfg.live) (hla : t3 ≤ t2 + cfg.live) :
    (Msg.hold r []).op ∈ ((b.tick fam cfg iy t1 : HeldM F Step) hb).1.send ∧
    let a' := ((a.recv fam cfg ix (Msg.hold r []).op.bytes t2 : HeldM F Step) ha).1.conn
    (Msg.rbsr r (a'.round + 1)
      ((window 0).map (opening Prod.fst Prod.snd sha256 cfg.params
        (ix.over cfg.params.depth r (max a'.floor pfa))))).op ∈
      ((a'.tick fam cfg ix t3 : HeldM F Step) ha).1.send := by
  refine ⟨responder_asks fam cfg iy b r t1 pfb hb hdb hpb hrb hlb fresh, ?_⟩
  intro a'
  obtain ⟨_, _, hdue⟩ := ask_due fam cfg ix a r t2 t3 ha hda hra idle
  have e : a' = ({ a with heard := t2 } : Conn).onAsk r := by
    simp [a', Conn.recv, Op.decode_bytes, ofOp_hold]
  obtain ⟨rs, ea⟩ := Conn.onAsk_eq ({ a with heard := t2 } : Conn) r
  have hd' : a'.dialer = true := by rw [e, ea]; exact hda
  have hp' : a'.peerFloor = some pfa := by rw [e, ea]; exact hpa
  have hr' : r ∈ a'.rooms := by rw [e, ea]; exact hra
  have hl' : t3 ≤ a'.heard + cfg.live := by rw [e, ea]; exact hla
  exact round_due fam cfg ix a' r t3 pfa ha hd' hp' hr' hl' (by rw [hdue]; rfl)

/-! ## Main's rounds, as they shipped: the negative control -/

section
variable {m : Type → Type} [Monad m] [Store F m]

/-- `Conn.work` as main shipped it until this change (b4d103a,
engine/sync/Conn.lean:446–454), its connection-wide timer passed in
(`lastRound`, and `every`, 30 000 by default): only the dialer opens
rounds, and only when its timer is due; the responder never asks (its
closure walk, since replaced by the window's set S, left out). A
negative control: it must never run. -/
def Conn.workShipped (every lastRound : Nat) (ix : Index) (c : Conn) (now : Nat) : m Step := do
  let c := c.expireAsks cfg now
  let s := if c.dialer && lastRound + every ≤ now then c.start cfg ix now else { conn := c }
  let due := c.lastAsk + cfg.retry ≤ now
  return { s with
    conn := { s.conn with lastAsk := if due then now else c.lastAsk }
    send := s.send ++ chunks cfg (c.retryIds cfg now) .want }

end

/-- **Main's rounds break `responder_asks`.** A responder that starts
showing a room sends no ask under main's work: it waits for the
dialer's next timer. -/
theorem shipped_responder_silent (every lastRound : Nat) (ix : Index) (c : Conn) (r : Id) (now : Nat)
    (h : Held F) (hd : c.dialer = false) :
    (Msg.hold r []).op ∉ ((c.workShipped cfg every lastRound ix now : HeldM F Step) h).1.send := by
  unfold Conn.workShipped
  simp only [HeldM.pure_apply, Conn.expireAsks, hd, Bool.false_and, Bool.false_eq_true,
    ite_false, List.nil_append]
  intro hm
  obtain ⟨l, _, e⟩ := List.mem_map.1 hm
  have := congrArg Op.kind e
  simp [Msg.op, kHave, kWant] at this

/-- **Main's rounds break `round_due`.** A dialer whose session starts
showing a room opens no round in it under main's work until its
connection-wide timer comes round: up to `every` later. -/
theorem shipped_dialer_waits (every lastRound : Nat) (ix : Index) (c : Conn) (r : Id) (now k : Nat)
    (cs : List Claim) (h : Held F) (early : now < lastRound + every) :
    (Msg.rbsr r k cs).op ∉ ((c.workShipped cfg every lastRound ix now : HeldM F Step) h).1.send := by
  obtain ⟨d, ed, _⟩ := work_base cfg c now
  unfold Conn.workShipped
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  rw [ed, if_neg (by simp; omega)]
  intro hm
  rcases List.mem_append.1 hm with hm | hm
  · cases hm
  · exact rbsr_not_chunk cfg r k cs _ _ (fun l => Or.inr rfl) hm

/-- Both controls' premises hold where the laws' do: a responder showing
a fresh room on a live session (`responder_asks` sends the ask; main's
work does not), and a dialer showing a fresh room within its timer
(`round_due` opens it; main's work does not). -/
theorem shipped_controls_apply (ix : Index) (r : Id) (h : Held F) :
    let b : Conn := { dialer := false, rooms := [r], floor := 0, peerFloor := some 0 }
    let a : Conn := { dialer := true, rooms := [r], floor := 0, peerFloor := some 0 }
    ((Msg.hold r []).op ∈ ((b.tick fam cfg ix 0 : HeldM F Step) h).1.send ∧
      (Msg.hold r []).op ∉ ((b.workShipped cfg 30000 0 ix 0 : HeldM F Step) h).1.send) ∧
    ((Msg.rbsr r (a.round + 1)
      ((window 0).map (opening Prod.fst Prod.snd sha256 cfg.params
        (ix.over cfg.params.depth r (max a.floor 0))))).op ∈
        ((a.tick fam cfg ix 0 : HeldM F Step) h).1.send ∧
      ∀ k cs, (Msg.rbsr r k cs).op ∉ ((a.workShipped cfg 30000 0 ix 0 : HeldM F Step) h).1.send) := by
  intro b a
  refine ⟨⟨responder_asks fam cfg ix b r 0 0 h rfl rfl (by simp [b]) (by simp [b]) rfl,
      shipped_responder_silent cfg 30000 0 ix b r 0 h rfl⟩,
    round_due fam cfg ix a r 0 0 h rfl rfl (by simp [a]) (by simp [a])
      (by simp [Conn.due, Conn.roundedAt, a]),
    fun k cs => shipped_dialer_waits cfg 30000 0 ix a r 0 k cs h (by decide)⟩

end

end Engine.Sync
